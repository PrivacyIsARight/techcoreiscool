function widget:GetInfo()
    return {
        name      = "TechCore Tracker",
        desc      = "TechcoreTracker: Displays techcore information and messages, can drag text boxes. Tracks number of techcore points and T2/T3 thresholds. Blocks T2/T3 lab blueprints unless team has enough techpoints. Enforces unit-sharing restrictions, only constructors allowed whilst T2/T3 are online. Auto-disables when not required.",        
	author    = "[APM]C3BO",
        date      = "11/09/2026",
        license   = "GPLv2",
        layer     = 0,
        enabled   = true,
        version   = "2.0",
    }
end

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

local CONFIG = {
    TECH_CORE_PARAM = "tech_core_value",
    TECH_CORE_VALUE = 1,

    BOX_WIDTH  = 210,
    BOX_HEIGHT = 72,
    TITLE_SIZE = 14,
    VALUE_SIZE = 18,
    MESSAGE_X = 0.5,
    MESSAGE_Y = 0.85,
    MESSAGE_SIZE = 54,
    MESSAGE_TIME = 10.0,
    RESCAN_FRAMES = 90,

    -- Permanent T2 warning (draggable, mid-left screen by default)
    WARN_TEXT     = "NO T2, INSUFFICIENT TECHCORES",
    WARN_SIZE     = 22,
    WARN_HITBOX_W = 400,
    WARN_HITBOX_H = 30,

    -- Permanent T1.5 message (draggable, positioned below the T2 warning by default)
    T15_TEXT      = "You can now build T1.5 constructor using the 1Mconturret.",
    T15_SIZE      = 25,
    T15_HITBOX_W  = 400,
    T15_HITBOX_H  = 26,

    ---------------------------------------------------------------------------
    -- Custom gameplay detection: the widget disables itself at game start
    -- when NO loaded unitdef carries the TECH_CORE_PARAM custom param at all
    -- (i.e. someone is playing a normal game without the techcore mod).
    -- See AnyUnitDefHasTechCoreParam() below - detection no longer depends
    -- on a hardcoded list of building names.
    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Tier restriction for T2/T3 lab blueprints (direct unitdef names)
    ---------------------------------------------------------------------------
    RESTRICT_LABS = true,

    TIER2_LABS = {
        "armalab", "coralab", "legalab",
        "armavp",  "coravp",  "legavp",
        "armaap",  "coraap",  "legaap",
        "armasy",  "corasy",  "legadvshipyard",
    },

    TIER3_LABS = {
        "armshltx", "armshltxuw",
        "corgant",  "corgantuw",
        "leggant",  "leggantuw",
    },

    -- "WE REQUIRE MORE CORES" warning (red, middle of the screen, 5 seconds)
    CORE_MSG_TEXT     = "WE REQUIRE MORE CORES",
    CORE_MSG_SIZE     = 48,
    CORE_MSG_X        = 0.5,
    CORE_MSG_Y        = 0.5,
    CORE_MSG_TIME     = 5.0,
    CORE_MSG_COOLDOWN = 1.0,   -- min seconds between re-shows (anti-spam)

    -- Last resort: if a locked lab starts construction anyway (e.g. placed by
    -- a teammate not running this widget), issue a self-destruct order to it.
    DESTROY_BLOCKED_LABS = true,

    ---------------------------------------------------------------------------
    -- Unit sharing restrictions
    --
    -- The engine handles the actual unit transfer itself, so a widget cannot
    -- block a share before it happens. Instead, every teammate running this
    -- widget watches shares as they land (UnitGiven) and, if the receiving
    -- player's own copy of the widget decides the share broke the rules, it
    -- immediately shares the unit back to whoever sent it.
    ---------------------------------------------------------------------------
    RESTRICT_SHARING = true,

    -- Sharing is only ever allowed while T2 or T3 is unlocked, and even then
    -- only for unitdefs on this list. Everything else is always illegal to
    -- share, regardless of tech level. Matched case-insensitively against
    -- UnitDefs[].name.
    SHAREABLE_UNIT_NAMES = {
        "armck", "corck", "legck",
        "armcv", "corcv", "legcv",
        "armca", "corca", "legca",
        "armcs", "corcs", "legnavyconship",
        "armcsa", "corcsa", "legspcon",
        "armbeaver", "cormuskrat", "legotter",
        "armch", "corch", "legch",
        "ARMACA", "CORACA", "LEGACA",
        "ARMACK", "CORACK", "LEGACK",
        "ARMACV", "CORACV", "LEGACV",
        "ARMACSUB", "CORACSUB", "leganavyconsub",
        "corprinter",
    },

    SHARE_VIOLATION_MSG = "Illegal share detected - unit returned to sender",
    SHARE_MSG_TIME      = 5.0,

    -- How many recent share events to keep for the /sharelog debug command.
    SHARE_LOG_MAX = 50,

    -- How long (seconds) a "this incoming unit is a rule-enforced return, not
    -- a fresh share" notice from another client stays valid for. Only needs
    -- to bridge normal network latency.
    SHARE_RETURN_NOTICE_TTL = 8.0,
}

--------------------------------------------------------------------------------
-- Locals
--------------------------------------------------------------------------------

local CMD = CMD

local myTeamID = nil
local myAllyTeamID = nil
local alliedTeams = {}

local startingPlayerCount = nil
local t2Threshold = 0
local t3Threshold = 0

local techCoreBuildings = {}
local techCoreCount = 0

local t2Unlocked = false
local t3Unlocked = false

local thresholdsInitialized = false
local notificationText = nil
local notificationUntil = 0
local lastRescanFrame = -CONFIG.RESCAN_FRAMES

-- Tier restriction state
local restrictedLabDefs = {}   -- unitDefID -> tier (2 or 3)
local nameToDefID = {}         -- lowercase unitdef name -> unitDefID
local coreMsgUntil = 0         -- os.clock() time the warning is shown until
local lastCoreMsgTime = 0      -- throttle for the warning
local lastGoodCmdID = nil      -- last allowed command id (restore target)

-- Custom gameplay detection state
local selfDisabled = false     -- true when no unitdef in this game carries the tech_core_value param
local removePending = false    -- deferred widgetHandler removal flag

-- Sharing restriction state
local shareableUnitDefIDs = {} -- unitDefID -> true (allowed to ever be shared)
local shareHistory = {}        -- ordered array of recent share records (debug/log, see /sharelog)
local expectingReturn = {}     -- unitID -> os.clock() expiry; an ally told us this incoming unit
                                -- is a rule-enforced return, not a fresh (re-)violation

-- Tech core box dragging
local boxX = 20
local boxY = 120
local isDragging = false
local dragOffsetX = 0
local dragOffsetY = 0

-- Warning text dragging (-1 = not yet initialized)
local warnX = -1
local warnY = -1
local isDraggingWarn = false
local dragOffsetWarnX = 0
local dragOffsetWarnY = 0

-- T1.5 text dragging (-1 = not yet initialized)
local t15X = -1
local t15Y = -1
local isDraggingT15 = false
local dragOffsetT15X = 0
local dragOffsetT15Y = 0

local vsx, vsy = 800, 600
local gl = gl

--------------------------------------------------------------------------------
-- Utility
--------------------------------------------------------------------------------

local function IsTechCore(unitDefID)
    local ud = UnitDefs[unitDefID]
    if not ud or not ud.customParams then
        return false
    end
    local value = ud.customParams[CONFIG.TECH_CORE_PARAM]
    return tonumber(value) == CONFIG.TECH_CORE_VALUE
end

-- Gameplay detection: true as soon as ANY loaded unitdef carries the
-- tech_core_value custom param at all, regardless of its value. This is
-- deliberately looser than IsTechCore() (which also checks the value) -
-- it only needs to answer "is the techcore mod even loaded in this game".
local function AnyUnitDefHasTechCoreParam()
    for _, ud in pairs(UnitDefs) do
        if ud and ud.customParams and ud.customParams[CONFIG.TECH_CORE_PARAM] ~= nil then
            return true
        end
    end
    return false
end

local function ShowNotification(text)
    notificationText = text
    notificationUntil = os.clock() + CONFIG.MESSAGE_TIME
end

local function Notify(text)
    Spring.Echo("[Tech Core] " .. text)
    ShowNotification(text)
end

local function GetAlliedTeams()
    if not myAllyTeamID then
        if myTeamID then
            return {[myTeamID] = true}
        end
        return {}
    end
    local teams = Spring.GetTeamList(myAllyTeamID)
    if not teams or #teams == 0 then
        if myTeamID then
            return {[myTeamID] = true}
        end
        return {}
    end
    local t = {}
    for i = 1, #teams do
        t[teams[i]] = true
    end
    return t
end

local function GetStartingPlayerCount()
    if not myAllyTeamID then
        if not myTeamID then return 0 end
        local players = Spring.GetPlayerList(myTeamID, false)
        return (players and #players) or 0
    end
    local teams = Spring.GetTeamList(myAllyTeamID)
    if not teams or #teams == 0 then
        if not myTeamID then return 0 end
        local players = Spring.GetPlayerList(myTeamID, false)
        return (players and #players) or 0
    end
    local total = 0
    local gaiaTeamID = Spring.GetGaiaTeamID()
    for i = 1, #teams do
        local teamID = teams[i]
        local players = Spring.GetPlayerList(teamID, false)
        local numPlayers = (players and #players) or 0
        if numPlayers > 0 then
            total = total + numPlayers
        elseif teamID ~= gaiaTeamID then
            total = total + 1
        end
    end
    return total
end

local function SetThresholds(playerCount)
    startingPlayerCount = math.max(0, playerCount or 0)
    t2Threshold = startingPlayerCount
    t3Threshold = math.ceil(startingPlayerCount * 1.5)
end

local function UpdateUnlockState(allowMessages)
    local newT2Unlocked = (t2Threshold > 0 and techCoreCount >= t2Threshold)
    local newT3Unlocked = (t3Threshold > 0 and techCoreCount >= t3Threshold)

    if not thresholdsInitialized then
        t2Unlocked = newT2Unlocked
        t3Unlocked = newT3Unlocked
        thresholdsInitialized = true
        return false
    end

    local stateChanged = false
    local messages = {}

    if allowMessages then
        if newT2Unlocked and not t2Unlocked then
            table.insert(messages, "T2 unlocked\nYou can now share T1, T1.5 and T2cons")
            stateChanged = true
        elseif not newT2Unlocked and t2Unlocked then
            table.insert(messages, "T2 lost\nSharing no longer available")
            stateChanged = true
        end
        if newT3Unlocked and not t3Unlocked then
            table.insert(messages, "T3 unlocked")
            stateChanged = true
        elseif not newT3Unlocked and t3Unlocked then
            table.insert(messages, "T3 lost")
            stateChanged = true
        end
    end

    t2Unlocked = newT2Unlocked
    t3Unlocked = newT3Unlocked

    if stateChanged then
        Notify(table.concat(messages, "\n"))
    end
    return stateChanged
end

local function AddTechCore(unitID, allowMessages)
    if techCoreBuildings[unitID] then
        return false, false
    end
    techCoreBuildings[unitID] = true
    techCoreCount = techCoreCount + 1
    local stateChanged = UpdateUnlockState(allowMessages)
    return true, stateChanged
end

local function RemoveTechCore(unitID, allowMessages)
    if not techCoreBuildings[unitID] then
        return false, false
    end
    techCoreBuildings[unitID] = nil
    techCoreCount = math.max(0, techCoreCount - 1)
    local stateChanged = UpdateUnlockState(allowMessages)
    return true, stateChanged
end

local function ScanTeamTechCores(allowMessages)
    if not myAllyTeamID and not myTeamID then
        return
    end
    local found = {}
    for teamID in pairs(alliedTeams) do
        local units = Spring.GetTeamUnits(teamID)
        if units then
            for i = 1, #units do
                local unitID = units[i]
                local unitDefID = Spring.GetUnitDefID(unitID)
                if unitDefID and IsTechCore(unitDefID) then
                    local health, maxHealth, paralyzeDamage, captureProgress, buildProgress =
                        Spring.GetUnitHealth(unitID)
                    if buildProgress and buildProgress >= 1 then
                        found[unitID] = true
                    end
                end
            end
        end
    end
    techCoreBuildings = found
    local count = 0
    for _ in pairs(found) do
        count = count + 1
    end
    techCoreCount = count
    UpdateUnlockState(allowMessages)
end

local function InitializeThresholds()
    local playerCount = GetStartingPlayerCount()
    if playerCount > 0 then
        SetThresholds(playerCount)
        return true
    end
    return false
end

local function EnsureThresholds()
    if startingPlayerCount ~= nil then
        return
    end
    if InitializeThresholds() then
        ScanTeamTechCores(false)
    end
end

-- Check if the local player owns at least one completed and alive tech core
local function HasOwnTechCore()
    if not myTeamID then
        return false
    end
    local units = Spring.GetTeamUnits(myTeamID)
    if not units then
        return false
    end
    for i = 1, #units do
        local unitID = units[i]
        local unitDefID = Spring.GetUnitDefID(unitID)
        if unitDefID and IsTechCore(unitDefID) then
            local health, maxHealth, paralyzeDamage, captureProgress, buildProgress =
                Spring.GetUnitHealth(unitID)
            if buildProgress and buildProgress >= 1 then
                if (not health) or health > 0 then
                    return true
                end
            end
        end
    end
    return false
end

--------------------------------------------------------------------------------
-- Tier restriction for T2/T3 lab blueprints (direct unitdef names)
--------------------------------------------------------------------------------

-- Builds the unitDefID -> tier map from the hardcoded name lists.
local function BuildRestrictedLabDefs()
    local restrictedNames = {}
    for i = 1, #CONFIG.TIER2_LABS do
        restrictedNames[string.lower(CONFIG.TIER2_LABS[i])] = 2
    end
    for i = 1, #CONFIG.TIER3_LABS do
        restrictedNames[string.lower(CONFIG.TIER3_LABS[i])] = 3
    end

    restrictedLabDefs = {}
    nameToDefID = {}
    for unitDefID, ud in pairs(UnitDefs) do
        if ud and ud.name then
            local lowerName = string.lower(ud.name)
            nameToDefID[lowerName] = unitDefID
            local tier = restrictedNames[lowerName]
            if tier then
                restrictedLabDefs[unitDefID] = tier
            end
        end
    end
end

local function GetLabTier(unitDefID)
    return restrictedLabDefs[unitDefID]
end

local function TeamHasTierUnlocked(tier)
    if tier == 2 then
        return t2Unlocked
    elseif tier == 3 then
        return t3Unlocked
    end
    return true
end

--------------------------------------------------------------------------------
-- Unit sharing restrictions
--------------------------------------------------------------------------------

-- Builds the unitDefID set of everything ever allowed to be shared. Relies
-- on nameToDefID, which BuildRestrictedLabDefs() populates for every unitdef
-- in the game, so call this after BuildRestrictedLabDefs().
local function BuildShareableUnitDefs()
    shareableUnitDefIDs = {}
    for i = 1, #CONFIG.SHAREABLE_UNIT_NAMES do
        local defID = nameToDefID[string.lower(CONFIG.SHAREABLE_UNIT_NAMES[i])]
        if defID then
            shareableUnitDefIDs[defID] = true
        end
    end
end

-- True if this unitdef is currently legal to share to a teammate.
local function IsShareAllowed(unitDefID)
    if not CONFIG.RESTRICT_SHARING then
        return true
    end
    if not (t2Unlocked or t3Unlocked) then
        -- Sharing (of anything) is off the table until T2 or T3 is unlocked.
        return false
    end
    return shareableUnitDefIDs[unitDefID] == true
end

-- Records a share event for the /sharelog debug command and echoes it.
local function LogShare(unitID, unitDefID, fromTeam, toTeam, legal)
    local ud = UnitDefs[unitDefID]
    local name = (ud and ud.name) or tostring(unitDefID)

    table.insert(shareHistory, {
        unitID   = unitID,
        name     = name,
        fromTeam = fromTeam,
        toTeam   = toTeam,
        time     = os.clock(),
        legal    = legal,
    })
    while #shareHistory > CONFIG.SHARE_LOG_MAX do
        table.remove(shareHistory, 1)
    end

    Spring.Echo(string.format(
        "[Tech Core] Share: team %d -> team %d | %s (unitID %d) | %s",
        fromTeam, toTeam, name, unitID, legal and "allowed" or "ILLEGAL"
    ))
end

-- Shares a specific set of units to targetTeamID without disturbing the
-- player's current unit selection. The engine's ShareResources call only
-- operates on the current selection, so we swap it out and back.
-- Wrapped in pcall throughout: this must never be able to crash the widget.
local function ShareUnitsTo(targetTeamID, unitIDs)
    local gotSelection, prevSelection = pcall(Spring.GetSelectedUnits)
    if not gotSelection then
        prevSelection = {}
    end

    local selectOk = pcall(Spring.SelectUnitArray, unitIDs)
    local shareOk = false
    if selectOk then
        shareOk = pcall(Spring.ShareResources, targetTeamID, "units")
    end
    pcall(Spring.SelectUnitArray, prevSelection)

    return selectOk and shareOk
end

local function RestrictionsReady()
    -- Don't enforce anything until the thresholds are properly initialized,
    -- otherwise everything would count as locked at game start.
    return CONFIG.RESTRICT_LABS
        and thresholdsInitialized
        and startingPlayerCount ~= nil
        and startingPlayerCount > 0
end

-- Returns true when the blueprint must be blocked.
local function BlockLabBlueprint(unitDefID, source)
    if not RestrictionsReady() then
        return false
    end

    local tier = GetLabTier(unitDefID)
    if not tier then
        return false
    end

    if TeamHasTierUnlocked(tier) then
        return false
    end

    -- Red warning, middle of the screen, 5 seconds (throttled anti-spam).
    local now = os.clock()
    if (now - lastCoreMsgTime) >= CONFIG.CORE_MSG_COOLDOWN then
        lastCoreMsgTime = now
        coreMsgUntil = now + CONFIG.CORE_MSG_TIME

        local ud = UnitDefs[unitDefID]
        local threshold = (tier == 2) and t2Threshold or t3Threshold
        Spring.Echo(string.format(
            "[Tech Core] Blocked %s (T%d lab via %s, %d/%d tech cores): %s",
            (ud and (ud.translatedHumanName or ud.humanName or ud.name)) or tostring(unitDefID),
            tier, tostring(source), techCoreCount, threshold, CONFIG.CORE_MSG_TEXT
        ))
    end
    return true
end

-- Deselect the loaded blueprint, preferring to restore the command that was
-- active before the blocked lab was loaded. All engine calls are pcalled so
-- engine differences can never crash the widget.
-- Forcefully exit the build menu entirely, returning the constructor to
-- default (move) state. Clears lastGoodCmdID so we never restore into
-- another build cursor — the player must consciously re-enter the menu.
local function ForceExitBuildMenu()
    lastGoodCmdID = nil
    pcall(Spring.SetActiveCommand, 0)
    pcall(Spring.SetActiveCommand, -1)
end

--------------------------------------------------------------------------------
-- Widget lifecycle
--------------------------------------------------------------------------------

function widget:Initialize()
    myTeamID = Spring.GetMyTeamID()
    myAllyTeamID = Spring.GetMyAllyTeamID()
    alliedTeams = GetAlliedTeams()
    vsx, vsy = Spring.GetViewGeometry()

    boxX = math.max(0, math.min(boxX, vsx - CONFIG.BOX_WIDTH))
    boxY = math.max(0, math.min(boxY, vsy - CONFIG.BOX_HEIGHT))

    if warnX < 0 or warnY < 0 then
        warnX = 10
        warnY = math.floor(vsy * 0.5)
    end
    warnX = math.max(0, math.min(warnX, vsx - CONFIG.WARN_HITBOX_W))
    warnY = math.max(0, math.min(warnY, vsy - CONFIG.WARN_HITBOX_H))

    if t15X < 0 or t15Y < 0 then
        t15X = 10
        t15Y = warnY + CONFIG.WARN_SIZE + 6
    end
    t15X = math.max(0, math.min(t15X, vsx - CONFIG.T15_HITBOX_W))
    t15Y = math.max(0, math.min(t15Y, vsy - CONFIG.T15_HITBOX_H))

    BuildRestrictedLabDefs()

    ----------------------------------------------------------------------
    -- Custom gameplay check: if no loaded unitdef carries the
    -- tech_core_value custom param, this is a normal game - disable the
    -- widget entirely.
    ----------------------------------------------------------------------
    if not AnyUnitDefHasTechCoreParam() then
        selfDisabled = true
        removePending = true
        Spring.Echo(string.format(
            "[Tech Core Tracker] No unitdef in this game carries customParams.%s - normal game detected, widget disabled itself.",
            CONFIG.TECH_CORE_PARAM
        ))
        return
    end

    BuildShareableUnitDefs()

    InitializeThresholds()
    ScanTeamTechCores(false)
    thresholdsInitialized = false
    if startingPlayerCount and startingPlayerCount > 0 then
        UpdateUnlockState(false)
    end

    -- One status line so problems can never be silent.
    local restrictedCount = 0
    for _ in pairs(restrictedLabDefs) do
        restrictedCount = restrictedCount + 1
    end
    local listedNames = #CONFIG.TIER2_LABS + #CONFIG.TIER3_LABS
    local shareableCount = 0
    for _ in pairs(shareableUnitDefIDs) do
        shareableCount = shareableCount + 1
    end
    Spring.Echo(string.format(
        "[Tech Core] Widget active. restrictions %s | players=%s cores=%d | T2 %d/%d (%s) | T3 %d/%d (%s) | restricted labs matched: %d/%d names | shareable units matched: %d/%d names (type /labtiers, /sharelog)",
        RestrictionsReady() and "ACTIVE" or "INACTIVE",
        tostring(startingPlayerCount),
        techCoreCount,
        techCoreCount, t2Threshold, t2Unlocked and "unlocked" or "LOCKED",
        techCoreCount, t3Threshold, t3Unlocked and "unlocked" or "LOCKED",
        restrictedCount, listedNames,
        shareableCount, #CONFIG.SHAREABLE_UNIT_NAMES
    ))
end

-- Deferred self-removal (normal game without techcores). Runs on the first
-- frame after Initialize, when the widget is guaranteed to be fully
-- registered with the handler. NOTE: this Update makes NO Spring API calls
-- at all, so it cannot reintroduce the earlier GetActiveCmdDesc crash.
function widget:Update(dt)
    if selfDisabled and removePending then
        removePending = false
        if widgetHandler and widgetHandler.RemoveWidget then
            -- try with the explicit widget reference first; fall back to the
            -- argument-less form some handler versions expect
            if not pcall(widgetHandler.RemoveWidget, widgetHandler, widget) then
                pcall(widgetHandler.RemoveWidget, widgetHandler)
            end
        end
    end
end

function widget:ViewResize(viewSizeX, viewSizeY)
    vsx = viewSizeX
    vsy = viewSizeY
    boxX = math.max(0, math.min(boxX, vsx - CONFIG.BOX_WIDTH))
    boxY = math.max(0, math.min(boxY, vsy - CONFIG.BOX_HEIGHT))
    warnX = math.max(0, math.min(warnX, vsx - CONFIG.WARN_HITBOX_W))
    warnY = math.max(0, math.min(warnY, vsy - CONFIG.WARN_HITBOX_H))
    t15X  = math.max(0, math.min(t15X,  vsx - CONFIG.T15_HITBOX_W))
    t15Y  = math.max(0, math.min(t15Y,  vsy - CONFIG.T15_HITBOX_H))
end

function widget:Shutdown()
    techCoreBuildings = {}
    notificationText = nil
    coreMsgUntil = 0
    lastGoodCmdID = nil
    shareHistory = {}
    expectingReturn = {}
end

function widget:GetConfigData()
    return {
        boxX  = boxX,
        boxY  = boxY,
        warnX = warnX,
        warnY = warnY,
        t15X  = t15X,
        t15Y  = t15Y,
    }
end

function widget:SetConfigData(data)
    if data then
        if data.boxX  then boxX  = data.boxX  end
        if data.boxY  then boxY  = data.boxY  end
        if data.warnX then warnX = data.warnX end
        if data.warnY then warnY = data.warnY end
        if data.t15X  then t15X  = data.t15X  end
        if data.t15Y  then t15Y  = data.t15Y  end
    end
end

--------------------------------------------------------------------------------
-- Mouse Interaction
--------------------------------------------------------------------------------

function widget:MousePress(x, y, button)
    if selfDisabled then
        return false
    end
    if button ~= 1 then
        return false
    end

    -- T1.5 message: draggable whenever it is visible
    if t15X >= 0 and t15Y >= 0 and HasOwnTechCore() then
        if x >= t15X and x <= t15X + CONFIG.T15_HITBOX_W
           and y >= t15Y and y <= t15Y + CONFIG.T15_HITBOX_H then
            isDraggingT15 = true
            dragOffsetT15X = x - t15X
            dragOffsetT15Y = y - t15Y
            return true
        end
    end

    -- T2 warning: draggable only when T2 is not unlocked
    if not t2Unlocked and warnX >= 0 and warnY >= 0 then
        if x >= warnX and x <= warnX + CONFIG.WARN_HITBOX_W
           and y >= warnY and y <= warnY + CONFIG.WARN_HITBOX_H then
            isDraggingWarn = true
            dragOffsetWarnX = x - warnX
            dragOffsetWarnY = y - warnY
            return true
        end
    end

    -- Tech core box
    if x >= boxX and x <= boxX + CONFIG.BOX_WIDTH
       and y >= boxY and y <= boxY + CONFIG.BOX_HEIGHT then
        isDragging = true
        dragOffsetX = x - boxX
        dragOffsetY = y - boxY
        return true
    end

    return false
end

function widget:MouseMove(x, y, dx, dy, button)
    if isDragging then
        boxX = x - dragOffsetX
        boxY = y - dragOffsetY
        boxX = math.max(0, math.min(boxX, vsx - CONFIG.BOX_WIDTH))
        boxY = math.max(0, math.min(boxY, vsy - CONFIG.BOX_HEIGHT))
        return true
    end
    if isDraggingWarn then
        warnX = x - dragOffsetWarnX
        warnY = y - dragOffsetWarnY
        warnX = math.max(0, math.min(warnX, vsx - CONFIG.WARN_HITBOX_W))
        warnY = math.max(0, math.min(warnY, vsy - CONFIG.WARN_HITBOX_H))
        return true
    end
    if isDraggingT15 then
        t15X = x - dragOffsetT15X
        t15Y = y - dragOffsetT15Y
        t15X = math.max(0, math.min(t15X, vsx - CONFIG.T15_HITBOX_W))
        t15Y = math.max(0, math.min(t15Y, vsy - CONFIG.T15_HITBOX_H))
        return true
    end
    return false
end

function widget:MouseRelease(x, y, button)
    if button ~= 1 then
        return false
    end
    if isDragging then
        isDragging = false
        return true
    end
    if isDraggingWarn then
        isDraggingWarn = false
        return true
    end
    if isDraggingT15 then
        isDraggingT15 = false
        return true
    end
    return false
end

--------------------------------------------------------------------------------
-- Unit events
--------------------------------------------------------------------------------

function widget:UnitCreated(unitID, unitDefID, unitTeam)
    if selfDisabled then
        return
    end
    -- LAST-RESORT NET: a locked lab started construction anyway (e.g. placed
    -- by a teammate not running this widget, or if the placement block
    -- failed on this engine build).
    if CONFIG.RESTRICT_LABS and alliedTeams[unitTeam] and RestrictionsReady() then
        local tier = GetLabTier(unitDefID)
        if tier and not TeamHasTierUnlocked(tier) then
            local ud = UnitDefs[unitDefID]
            coreMsgUntil = os.clock() + CONFIG.CORE_MSG_TIME
            Spring.Echo(string.format(
                "[Tech Core] A LOCKED T%d lab (%s) started construction! %s",
                tier,
                (ud and ud.name) or tostring(unitDefID),
                CONFIG.CORE_MSG_TEXT
            ))
            if CONFIG.DESTROY_BLOCKED_LABS then
                pcall(Spring.GiveOrderToUnit, unitID, CMD.SELFD, {}, {})
                Spring.Echo("[Tech Core] Self-destruct order issued to the locked lab.")
            end
        end
    end
end

function widget:UnitFinished(unitID, unitDefID, unitTeam)
    if selfDisabled then
        return
    end
    if alliedTeams[unitTeam] and IsTechCore(unitDefID) then
        EnsureThresholds()
        local added, stateChanged = AddTechCore(unitID, true)
        if added and not stateChanged then
            Notify(string.format(
                "Tech core completed: %d/%d T2 | %d/%d T3",
                techCoreCount, t2Threshold, techCoreCount, t3Threshold
            ))
        end
    end
end

function widget:UnitDestroyed(unitID, unitDefID, unitTeam)
    if selfDisabled then
        return
    end
    if alliedTeams[unitTeam] and IsTechCore(unitDefID) then
        RemoveTechCore(unitID, true)
    end
end

function widget:UnitGiven(unitID, unitDefID, newTeam, oldTeam)
    if selfDisabled then
        return
    end
    if alliedTeams[newTeam] and IsTechCore(unitDefID) then
        local _, _, _, _, buildProgress = Spring.GetUnitHealth(unitID)
        if buildProgress and buildProgress >= 1 then
            EnsureThresholds()
            AddTechCore(unitID, true)
        end
    end

    ----------------------------------------------------------------------
    -- Sharing restriction enforcement.
    --
    -- Every allied teammate's widget sees this callin (that's how allied
    -- vision works), but only the team that actually just received the
    -- unit (newTeam == myTeamID) is able to select it and share it back -
    -- you can only ever select/order your own team's units. So only that
    -- one client acts; everyone else just logs the event for /sharelog.
    ----------------------------------------------------------------------
    if CONFIG.RESTRICT_SHARING and oldTeam ~= newTeam and alliedTeams[oldTeam] and alliedTeams[newTeam] then
        local isExpectedReturn = false
        local expiry = expectingReturn[unitID]
        if expiry and expiry >= os.clock() then
            isExpectedReturn = true
            expectingReturn[unitID] = nil
        end

        if newTeam == myTeamID then
            local legal = IsShareAllowed(unitDefID)
            LogShare(unitID, unitDefID, oldTeam, newTeam, legal or isExpectedReturn)

            if not legal and not isExpectedReturn then
                -- v2.0: no local cooldown backstop here anymore - every
                -- illegal share that isn't a recognized return (see
                -- isExpectedReturn above) is returned immediately, every
                -- time. The only loop protection left is the TCT_RETURN
                -- notice below; if that notice is delayed or dropped, a
                -- returned unit CAN bounce back and forth between two
                -- clients with no hard stop.
                pcall(Spring.SendLuaUIMsg, "TCT_RETURN:" .. unitID, "a")

                if ShareUnitsTo(oldTeam, { unitID }) then
                    ShowNotification(CONFIG.SHARE_VIOLATION_MSG)
                    Spring.Echo(string.format(
                        "[Tech Core] Returned illegal share of %s (unitID %d) back to team %d.",
                        (UnitDefs[unitDefID] and UnitDefs[unitDefID].name) or tostring(unitDefID),
                        unitID, oldTeam
                    ))
                else
                    Spring.Echo(string.format(
                        "[Tech Core] WARNING: failed to auto-return illegally shared unit %d (ModUICtrl may be disabled).",
                        unitID
                    ))
                end
            end
        else
            -- We're just an observer of this share (a teammate other than
            -- the recipient) - log it, but only the recipient's client acts.
            LogShare(unitID, unitDefID, oldTeam, newTeam, IsShareAllowed(unitDefID) or isExpectedReturn)
        end
    end
end

-- Cross-client coordination for the sharing-restriction return mechanism.
-- See the "TCT_RETURN:" message sent from widget:UnitGiven above.
function widget:RecvLuaMsg(msg, playerID)
    if selfDisabled or not CONFIG.RESTRICT_SHARING then
        return
    end
    -- SendLuaUIMsg's "allies" broadcast is echoed back to the sender too, so
    -- ignore our own notices - otherwise a client that just returned a unit
    -- would mark itself as "expecting a return" for that unit, and would
    -- then wrongly wave through a genuinely new illegal share of the same
    -- unit later on instead of returning it.
    local ok, myPlayerID = pcall(Spring.GetMyPlayerID)
    if ok and playerID == myPlayerID then
        return
    end
    local idStr = string.match(msg or "", "^TCT_RETURN:(%d+)$")
    if idStr then
        local unitID = tonumber(idStr)
        if unitID then
            expectingReturn[unitID] = os.clock() + CONFIG.SHARE_RETURN_NOTICE_TTL
        end
    end
end

function widget:UnitTaken(unitID, unitDefID, oldTeam, newTeam)
    if selfDisabled then
        return
    end
    if alliedTeams[oldTeam] and IsTechCore(unitDefID) then
        RemoveTechCore(unitID, true)
    end
end

--------------------------------------------------------------------------------
-- Safety rescan
--------------------------------------------------------------------------------

function widget:GameFrame(frame)
    if selfDisabled then
        return
    end
    EnsureThresholds()
    if frame - lastRescanFrame >= CONFIG.RESCAN_FRAMES then
        lastRescanFrame = frame
        ScanTeamTechCores(false)
    end
end

--------------------------------------------------------------------------------
-- Tier restriction callins
--------------------------------------------------------------------------------

-- Fires the instant the player loads a blueprint (clicks a building in the
-- build menu). Build commands have a negative cmdID equal to -unitDefID.
function widget:ActiveCommandChanged(cmdID, cmdType, cmdName)
    cmdID = tonumber(cmdID)
    if not cmdID then
        return
    end

    if cmdID < 0 then
        if BlockLabBlueprint(-cmdID, "menu-select") then
            ForceExitBuildMenu()
            return
        end
        lastGoodCmdID = cmdID  -- allowed build ghost: valid restore target
    elseif cmdID > 0 then
        lastGoodCmdID = cmdID  -- allowed normal command: valid restore target
    end
end

-- Hard block: if a build command for a locked lab is about to be issued
-- (clicking to place the ghost), consume the click so the lab can never
-- actually be placed.
function widget:CommandNotify(cmdID, cmdParams, cmdOptions)
    cmdID = tonumber(cmdID)
    if cmdID and cmdID < 0 then
        if BlockLabBlueprint(-cmdID, "placement") then
            ForceExitBuildMenu()
            return true -- consume the command; the lab is never placed
        end
    end
    return false
end

--------------------------------------------------------------------------------
-- Debug command: /labtiers
--------------------------------------------------------------------------------

function widget:TextCommand(command)
    local cmd = string.lower(string.gsub(command or "", "^/+", ""))

    if cmd == "sharelog" then
        if #shareHistory == 0 then
            Spring.Echo("[Tech Core] No shares observed yet this game.")
            return true
        end
        Spring.Echo(string.format("[Tech Core] Last %d observed share(s):", #shareHistory))
        for i = 1, #shareHistory do
            local r = shareHistory[i]
            Spring.Echo(string.format("  team %d -> team %d | %-16s unitID=%-6d %s",
                r.fromTeam, r.toTeam, r.name, r.unitID,
                r.legal and "allowed" or "ILLEGAL (returned)"
            ))
        end
        return true
    end

    if cmd ~= "labtiers" then
        return false
    end

    Spring.Echo(string.format(
        "[Tech Core] Cores=%d | T2 %s (%d/%d) | T3 %s (%d/%d) | restrictions ready: %s",
        techCoreCount,
        t2Unlocked and "UNLOCKED" or "LOCKED", techCoreCount, t2Threshold,
        t3Unlocked and "UNLOCKED" or "LOCKED", techCoreCount, t3Threshold,
        tostring(RestrictionsReady())
    ))

    Spring.Echo(string.format(
        "[Tech Core] Gameplay detection: %s",
        AnyUnitDefHasTechCoreParam()
            and string.format("at least one unitdef carries customParams.%s", CONFIG.TECH_CORE_PARAM)
            or string.format("NO unitdef carries customParams.%s (widget would self-disable)", CONFIG.TECH_CORE_PARAM)
    ))

    local function ListNames(names, tier)
        for i = 1, #names do
            local defID = nameToDefID[string.lower(names[i])]
            if defID then
                Spring.Echo(string.format("  [T%d] %-16s defID=%-4d %s",
                    tier, names[i], defID,
                    TeamHasTierUnlocked(tier) and "(unlocked: buildable)" or "BLOCKED"))
            else
                Spring.Echo(string.format("  [!!] %-16s NOT FOUND in this game's unitdefs", names[i]))
            end
        end
    end

    Spring.Echo("[Tech Core] Tier 2 labs:")
    ListNames(CONFIG.TIER2_LABS, 2)
    Spring.Echo("[Tech Core] Tier 3 labs:")
    ListNames(CONFIG.TIER3_LABS, 3)

    Spring.Echo(string.format(
        "[Tech Core] Sharing: %s (T2 or T3 required, plus this list):",
        (t2Unlocked or t3Unlocked) and "CURRENTLY ALLOWED for listed units" or "CURRENTLY ALL BLOCKED (no T2/T3)"
    ))
    for i = 1, #CONFIG.SHAREABLE_UNIT_NAMES do
        local name = CONFIG.SHAREABLE_UNIT_NAMES[i]
        local defID = nameToDefID[string.lower(name)]
        Spring.Echo(string.format("  %-16s %s",
            name,
            defID and ("defID=" .. defID) or "NOT FOUND in this game's unitdefs"
        ))
    end
    Spring.Echo("[Tech Core] Type /sharelog to see recently observed shares.")
    return true
end

--------------------------------------------------------------------------------
-- Drawing
--------------------------------------------------------------------------------

local function DrawBox(x, y, width, height)
    gl.Color(0.02, 0.02, 0.02, 0.78)
    gl.Rect(x, y, x + width, y + height)
    gl.Color(0.75, 0.75, 0.75, 0.8)
    gl.LineWidth(1.5)
    gl.BeginEnd(GL.LINE_LOOP, function()
        gl.Vertex(x, y)
        gl.Vertex(x + width, y)
        gl.Vertex(x + width, y + height)
        gl.Vertex(x, y + height)
    end)
    gl.LineWidth(1)
end

local function DrawTierLine(label, count, threshold, unlocked, x, y)
    local status = string.format("%d/%d", count, threshold)
    if unlocked then
        gl.Color(0.3, 1.0, 0.3, 1.0)
    else
        gl.Color(1.0, 1.0, 1.0, 1.0)
    end
    gl.Text(label, x, y, CONFIG.VALUE_SIZE, "o")
    gl.Text(status, x + 55, y, CONFIG.VALUE_SIZE, "o")
end

function widget:DrawScreen()
    if selfDisabled then
        return
    end

    --------------------------------------------------------------------------
    -- Tech core counter box
    --------------------------------------------------------------------------

    local x = boxX
    local y = boxY

    DrawBox(x, y, CONFIG.BOX_WIDTH, CONFIG.BOX_HEIGHT)

    gl.Color(1.0, 1.0, 1.0, 1.0)
    gl.Text("TECH CORE", x + 10, y + CONFIG.BOX_HEIGHT - 18, CONFIG.TITLE_SIZE, "o")

    DrawTierLine("T2", techCoreCount, t2Threshold, t2Unlocked, x + 10, y + 28)
    DrawTierLine("T3", techCoreCount, t3Threshold, t3Unlocked, x + 105, y + 28)

    --------------------------------------------------------------------------
    -- T1.5 MESSAGE (green)
    --------------------------------------------------------------------------

    if HasOwnTechCore() then
        gl.Color(0.3, 1.0, 0.3, 1.0)
        gl.Text(
            CONFIG.T15_TEXT,
            t15X,
            t15Y,
            CONFIG.T15_SIZE,
            "O"
        )
    end

    --------------------------------------------------------------------------
    -- PERMANENT T2 WARNING (red, shown only while T2 is not unlocked)
    --------------------------------------------------------------------------

    if not t2Unlocked then
        gl.Color(1.0, 0.0, 0.0, 1.0)
        gl.Text(
            CONFIG.WARN_TEXT,
            warnX,
            warnY,
            CONFIG.WARN_SIZE,
            "O"
        )
    end

    --------------------------------------------------------------------------
    -- Temporary notification (red, big letters, top of screen)
    --------------------------------------------------------------------------

    if notificationText then
        local now = os.clock()
        local remaining = notificationUntil - now
        if remaining > 0 then
            local alpha = 1.0
            if remaining < 0.5 then
                alpha = remaining / 0.5
            end
            gl.Color(1.0, 0.0, 0.0, alpha)
            gl.Text(
                notificationText,
                vsx * CONFIG.MESSAGE_X,
                vsy * CONFIG.MESSAGE_Y,
                CONFIG.MESSAGE_SIZE,
                "ocO"
            )
        else
            notificationText = nil
        end
    end

    --------------------------------------------------------------------------
    -- "WE REQUIRE MORE CORES" warning (red, middle of screen, 5 seconds)
    --------------------------------------------------------------------------

    if coreMsgUntil > 0 then
        local now = os.clock()
        local remaining = coreMsgUntil - now
        if remaining <= 0 then
            coreMsgUntil = 0
        else
            local alpha = 1.0
            local elapsed = CONFIG.CORE_MSG_TIME - remaining
            if elapsed < 0.2 then
                alpha = elapsed / 0.2                     -- quick fade-in
            end
            if remaining < 0.5 then
                alpha = math.min(alpha, remaining / 0.5)  -- fade-out
            end
            gl.Color(1.0, 0.0, 0.0, alpha)
            gl.Text(
                CONFIG.CORE_MSG_TEXT,
                vsx * CONFIG.CORE_MSG_X,
                vsy * CONFIG.CORE_MSG_Y - CONFIG.CORE_MSG_SIZE * 0.4,
                CONFIG.CORE_MSG_SIZE,
                "ocO"
            )
        end
    end
end
