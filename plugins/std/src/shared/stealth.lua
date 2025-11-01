jit = {
    opt = {
        start = _G.jit.opt.start
    },
    util = {
        funcbc = _G.jit.util.funcbc,
        funcinfo = _G.jit.util.funcinfo
    },
    arch = _G.jit.arch,
    os = _G.jit.os,
    version = _G.jit.version,
    version_num = _G.jit.version_num,
    attach = _G.jit.attach,
    flush = _G.jit.flush,
    off = _G.jit.off,
    on = _G.jit.on,
    status = _G.jit.status
}

local isfunction = isfunction
local isnumber = isnumber
local unpack = unpack
local FindMetaTable = FindMetaTable

local environment = getfenv(1)
local traces = {}

local hooks = {}

local tableclones = {} --> map: detour => clone
local originalmetatables = {} --> map: detour => metatable
local vmeventsdetour = nil --> contains the detour metatable
local vmeventsclone = {}

--> luajit hashing functions reconstructed from the source code
local function lj_rol(x, n)
    return bit.bor(bit.lshift(x, n), bit.rshift(x, 32 - n))
end
local function hashidx(h)
    return bit.lshift(h, 3)
end
local function hashstring(s)
    local len = string.len(s)
    local h = len
    for i = 1, len do
        local p = string.byte(s, i)
        h = bit.bxor(h, lj_rol(h, 6) + p)
    end

    return hashidx(h)
end

local hashed = {
    [hashstring("bc")] = "bc",
    [hashstring("trace")] = "trace",
    [hashstring("record")] = "record",
    [hashstring("texit")] = "texit"
}

local hashed2 = {
    ["bc"] = hashstring("bc"),
    ["trace"] = hashstring("trace"),
    ["record"] = hashstring("record"),
    ["texit"] = hashstring("texit")
}

--> safely gets the type of the given object
local function safetype(object)
    local metatable = debug.getmetatable(object)
    if (not metatable) then
        return type(object)
    end

    local typefunc = rawget(metatable, "__type")
    if (typefunc) then
        rawset(metatable, "__type", nil)
        local t = type(object)
        rawset(metatable, "__type", typefunc)
        return t
    else
        return type(object)
    end
end

local function detourmetatable(object, clone, metatable)
    local original = originalmetatables[object]
    local new = {}

    if (istable(metatable)) then
        local key, value = next(metatable)
        ::clone_metatable::
        if (key) then
            new[key] = value

            key, value = next(metatable)
            goto clone_metatable
        end
    end

    local key, value = next(original)
    ::clone_detour::
    if (key) then
        new[key] = value

        key, value = next(metatable)
        goto clone_detour
    end

    debug.setmetatable(clone, metatable)
    return new
end

--> debug.sethook detours
Autorun.detour(debug.sethook, function(original, thread, hook, mask, count)
    if (rawequal(hook, nil)) then
        return original(thread, hook, mask, count)
    end

    local hasthread = safetype(thread) == "thread" --> If this is false, the arguments are the value to the left (so hook is really thread)
    local realcount = count
    local realhook = hook

    if (not hasthread) then
        realcount = mask
        realhook = thread
    end

    local detour = nil
    local targetcount = realcount
    if (isnumber(realcount)) then
        local counter = 0
        local safecount = tonumber(realcount)
        targetcount = 1
        detour = function(event, line)
            if (rawequal(getfenv(2), environment)) then
                return
            end

            if (event == "count") then
                counter = counter + 1
                if (counter == safecount) then
                    counter = 0
                    return realhook(event, line)
                end
            else
                return realhook(event, line)
            end
        end
    else
        detour = function(event, line)
            if (rawequal(getfenv(2), environment)) then
                return
            end

            return realhook(event, line)
        end
    end
    
    if (hasthread) then
        hooks[detour] = hook
        return original(thread, detour, mask, targetcount)
    else
        hooks[detour] = thread
        return original(detour, hook, targetcount)
    end
end)
Autorun.detour(debug.gethook, function(original, thread)
    local hook, mask, count = original(thread)
    if (not hook) then
        return nil
    end

    return hooks[hook], mask, count
end)

--> main jit.attach detours
Autorun.detour(jit.attach, function(original, callback, event)
    local hash = hashed2[event]
    if (hash) then
        rawset(vmeventsclone, hash, callback)
    end

    if (isfunction(callback)) then
        if (rawequal(event, "bc")) then
            local function detour(func)
                if (rawequal(getfenv(func), environment)) then
                    return
                end

                return callback(func)
            end

            return original(detour, event)
        elseif (rawequal(event, "trace")) then
            local function detour(what, tr, func, pc, otr, oex)
                if (rawequal(getfenv(func), environment)) then
                    return
                end

                return callback(what, tr, func, pc, otr, oex)
            end

            return original(detour, event)
        elseif (rawequal(event, "record")) then
            local function detour(tr, func, pc, depth)
                if (rawequal(getfenv(func), environment)) then
                    traces[tr] = true
                    return
                end

                return callback(tr, func, pc, depth)
            end

            return original(detour, event)
        elseif (rawequal(event, "texit")) then
            local function detour(tr, ex, ngpr, nfpr)
                if (traces[tr]) then
                    traces[tr] = nil
                    return
                end

                return callback(tr, ex, ngpr, nfpr)
            end

            return original(detour, event)
        end
    end

    return original(callback, event)
end)
Autorun.detour(FindMetaTable, function(original, metaname)
    if (rawequal(metaname, "_VMEVENTS")) then
        if (vmeventsdetour) then
            return vmeventsdetour
        end

        local vmevents = original(metaname) --> this cannot error so it's fine to do this
        vmeventsdetour = setmetatable({}, {
            __index = function(self, index, israw)
                if (israw) then
                    return rawget(vmeventsclone, index)
                end

                local metatable = debug.getmetatable(vmeventsclone)
                if (metatable) then
                    local __index = rawget(metatable, "__index")
                    if (__index) then
                        return __index(self, index)
                    end
                end

                return vmeventsclone[index]
            end,
            __newindex = function(self, index, value, israw)
                if (israw) then
                    local hash = hashed[index]
                    if (hash) then
                        jit.attach(value, hash)
                    else
                        rawset(vmeventsclone, index, value)
                        rawset(vmevents, index, value) --> this might not be necessary
                    end
                    
                    return
                end

                local metatable = debug.getmetatable(vmeventsclone)
                if (metatable) then
                    local __newindex = rawget(metatable, "__newindex")
                    if (__newindex) then
                        return __newindex(self, index, value) --> jit.attach is not called explicitly here because the __newindex callback would eventually either call rawset or do nothing
                    end
                end

                local hash = hashed[index]
                if (hash) then
                    jit.attach(value, hash)
                else
                    rawset(vmeventsclone, index, value)
                    rawset(vmevents, index, value) --> this might not be necessary
                end
            end
        })

        tableclones[vmeventsdetour] = vmeventsclone
        originalmetatables[vmeventsdetour] = debug.getmetatable(vmeventsdetour)

        return vmeventsdetour
    end

    return original(metaname)
end)

_G.getmetatable = Autorun.copyFastFunction(getmetatable, function(object)
    return getmetatable(tableclones[object] or object)
end)

_G.setmetatable = Autorun.copyFastFunction(setmetatable, function(object, metatable)
    local clone = tableclones[object]
    if (clone) then
        return setmetatable(object, detourmetatable(object, clone, metatable))
    else
        return setmetatable(object, metatable)
    end
end)

_G.debug.getmetatable = Autorun.copyFastFunction(debug.getmetatable, function(object)
    return debug.getmetatable(tableclones[object] or object)
end)

_G.debug.setmetatable = Autorun.copyFastFunction(debug.setmetatable, function(object, metatable)
    local clone = tableclones[object]
    if (clone) then
        return debug.setmetatable(object, detourmetatable(object, clone, metatable))
    else
        return debug.setmetatable(object, metatable)
    end
end)

_G.rawget = Autorun.copyFastFunction(rawget, function(object, index)
    local clone = tableclones[object]
    if (clone) then
        return rawget(debug.getmetatable(clone), "__index")(object, index, true)
    else
        return debug.setmetatable(object, metatable)
    end
end)

_G.rawset = Autorun.copyFastFunction(rawset, function(object, index, value)
    local clone = tableclones[object]
    if (clone) then
        return rawget(debug.getmetatable(clone), "__newindex")(object, index, value, true)
    else
        return debug.setmetatable(object, metatable)
    end
end)

_G.next = Autorun.copyFastFunction(next, function(object, previous)
    return next(tableclones[object] or object, previous)
end)

local nextdetour = _G.next
_G.pairs = Autorun.copyFastFunction(pairs, function(...)
    if (select("#", ...) == 0) then
        return error(string.format("bad argument #1 to '%s' (value expected)", debug.getinfo(1, "n").name))
    end

    local object = ...
    return nextdetour, object, nil
end)

_G.ipairs = Autorun.copyFastFunction(ipairs, function(object)
    return ipairs(tableclones[object] or object)
end)

for index, value in pairs(_G.table) do
    _G.table[index] = Autorun.copyFastFunction(value, function(object, ...)
        return value(tableclones[object] or object, ...)
    end)
end