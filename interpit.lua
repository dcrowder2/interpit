--[[
interpit.lua
Dakota Crowder
2018 April 10
CSCE A331 Spring 2018
Assignment 6
Modified code from:
--]]


-- interpit.lua  INCOMPLETE
-- Glenn G. Chappell
-- 29 Mar 2018
-- Updated 2 Apr 2018
--
-- For CS F331 / CSCE A331 Spring 2018
-- Interpret AST from parseit.parse
-- For Assignment 6, Exercise B


-- *******************************************************************
-- * To run a Dugong program, use dugong.lua (which uses this file). *
-- *******************************************************************


local interpit = {}  -- Our module


-- ***** Variables *****


-- Symbolic Constants for AST

local STMT_LIST   = 1
local INPUT_STMT  = 2
local PRINT_STMT  = 3
local FUNC_STMT   = 4
local CALL_FUNC   = 5
local IF_STMT     = 6
local WHILE_STMT  = 7
local ASSN_STMT   = 8
local CR_OUT      = 9
local STRLIT_OUT  = 10
local BIN_OP      = 11
local UN_OP       = 12
local NUMLIT_VAL  = 13
local BOOLLIT_VAL = 14
local SIMPLE_VAR  = 15
local ARRAY_VAR   = 16


-- ***** Utility Functions *****


-- numToInt
-- Given a number, return the number rounded toward zero.
local function numToInt(n)
    assert(type(n) == "number")

    if n >= 0 then
        return math.floor(n)
    else
        return math.ceil(n)
    end
end


-- strToNum
-- Given a string, attempt to interpret it as an integer. If this
-- succeeds, return the integer. Otherwise, return 0.
local function strToNum(s)
    assert(type(s) == "string")

    -- Try to do string -> number conversion; make protected call
    -- (pcall), so we can handle errors.
    local success, value = pcall(function() return 0+s end)

    -- Return integer value, or 0 on error.
    if success then
        return numToInt(value)
    else
        return 0
    end
end


-- numToStr
-- Given a number, return its string form.
local function numToStr(n)
    assert(type(n) == "number")

    return ""..n
end


-- boolToInt
-- Given a boolean, return 1 if it is true, 0 if it is false.
local function boolToInt(b)
    assert(type(b) == "boolean")

    if b then
        return 1
    else
        return 0
    end
end


--numToInt
--Given a number, if 1 return true, otherwise return false
local function numToBool(i)
    assert(type(i), "number")
    if i == 0 then
      return false
    else
      return true
    end
end



-- astToStr
-- Given an AST, produce a string holding the AST in (roughly) Lua form,
-- with numbers replaced by names of symbolic constants used in parseit.
-- A table is assumed to represent an array.
-- See the Assignment 4 description for the AST Specification.
--
-- THIS FUNCTION IS INTENDED FOR USE IN DEBUGGING ONLY!
-- IT SHOULD NOT BE CALLED IN THE FINAL VERSION OF THE CODE.
function astToStr(x)
    local symbolNames = {
        "STMT_LIST", "INPUT_STMT", "PRINT_STMT", "FUNC_STMT",
        "CALL_FUNC", "IF_STMT", "WHILE_STMT", "ASSN_STMT", "CR_OUT",
        "STRLIT_OUT", "BIN_OP", "UN_OP", "NUMLIT_VAL", "BOOLLIT_VAL",
        "SIMPLE_VAR", "ARRAY_VAR"
    }
    if type(x) == "number" then
        local name = symbolNames[x]
        if name == nil then
            return "<Unknown numerical constant: "..x..">"
        else
            return name
        end
    elseif type(x) == "string" then
        return '"'..x..'"'
    elseif type(x) == "boolean" then
        if x then
            return "true"
        else
            return "false"
        end
    elseif type(x) == "table" then
        local first = true
        local result = "{"
        for k = 1, #x do
            if not first then
                result = result .. ","
            end
            result = result .. astToStr(x[k])
            first = false
        end
        result = result .. "}"
        return result
    elseif type(x) == "nil" then
        return "nil"
    else
        return "<"..type(x)..">"
    end
end


-- ***** Primary Function for Client Code *****


-- interp
-- Interpreter, given AST returned by parseit.parse.
-- Parameters:
--   ast     - AST constructed by parseit.parse
--   state   - Table holding Dugong variables & functions
--             - AST for function xyz is in state.f["xyz"]
--             - Value of simple variable xyz is in state.v["xyz"]
--             - Value of array item xyz[42] is in state.a["xyz"][42]
--   incall  - Function to call for line input
--             - incall() inputs line, returns string with no newline
--   outcall - Function to call for string output
--             - outcall(str) outputs str with no added newline
--             - To print a newline, do outcall("\n")
-- Return Value:
--   state, updated with changed variable values
function interpit.interp(ast, state, incall, outcall)
    -- Each local interpretation function is given the AST for the
    -- portion of the code it is interpreting. The function-wide
    -- versions of state, incall, and outcall may be used. The
    -- function-wide version of state may be modified as appropriate.


    function interp_stmt_list(ast)
      if ast ~= nil then
        for i = 2, #ast do
            interp_stmt(ast[i])
        end
      end
    end


    function interp_stmt(ast)
        local name, body, str

        if ast[1] == INPUT_STMT then
            body = ast[2]
            name = eval_expression(body)
            state.v[name] = strToNum(incall())
        elseif ast[1] == PRINT_STMT then
            for i = 2, #ast do
                body = ast[i]
                if body[1] == CR_OUT then
                    outcall("\n")
                elseif body[1] == STRLIT_OUT then
                    outcall(eval_expression(body))
                elseif body[1] == NUMLIT_VAL or type(body[1]) == "table" then
                    str = eval_expression(body)
                    outcall(numToStr(str))
                else
                    str = numToStr(process_lvalue(body))
                    outcall(str)
                end
            end
        elseif ast[1] == FUNC_STMT then
            name = ast[2]
            body = ast[3]
            state.f[name] = body
        elseif ast[1] == CALL_FUNC then
            name = ast[2]
            body = state.f[name]
            if body == nil then
                body = { STMT_LIST }  -- Default AST
            end
            interp_stmt_list(body)
        elseif ast[1] == IF_STMT then
            for i = 2, #ast do
              if ast[i][1] ~= STMT_LIST then
                if numToBool(eval_expression(ast[i])) then
                    interp_stmt_list(ast[i+1])
                    return
                end
              end
            end
                if #ast % 2 == 0 then
                  interp_stmt_list(ast[#ast])
                end
        elseif ast[1] == WHILE_STMT then
            --TODO
        else
            assert(ast[1] == ASSN_STMT)
            body = ast[2]
            name, array = eval_expression(body)
            if array then
              if state.a[name] == nil then
                state.a[name] = {}
              end
              state.a[name][eval_expression(body[3])] = eval_expression(ast[3])
            else
              body = ast[3]
              state.v[name] = eval_expression(body)
            end
        end
    end


    function eval_expression(body)
      if body[1] == SIMPLE_VAR then
        return body[2]
      elseif body[1] == NUMLIT_VAL then
        return strToNum(body[2])
      elseif body[1] == BOOLLIT_VAL then
        return boolToInt(body[2] == "true")
      elseif body[1] == STRLIT_OUT then
        str = body[2]
        return str:sub(2,str:len()-1)  -- Remove quotes
      elseif body[1] == ARRAY_VAR then
        return body[2], true
      elseif body[1] == CALL_FUNC then
        --TODO
      elseif type(body[1]) == "table" then
        if body[1][1] == UN_OP then
          if body[1][2] == "+" then
            return process_lvalue(body[2])
          elseif body[1][2] == "-" then
            return -(process_lvalue(body[2]))
          else
            return boolToInt(not numToBool(process_lvalue(body[2])))
          end
        elseif body[1][1] == BIN_OP then
          if body[1][2] == "+" then
            return process_lvalue(body[2]) + process_lvalue(body[3])
          elseif body[1][2] == "-" then
            return process_lvalue(body[2]) - process_lvalue(body[3])
          elseif body[1][2] == "*" then
            return process_lvalue(body[2]) * process_lvalue(body[3])
          elseif body[1][2] == "/" then
            if process_lvalue(body[3]) == 0 then
              return 0
            end
            return numToInt(process_lvalue(body[2]) / process_lvalue(body[3]))
          elseif body[1][2] == "%" then
            if process_lvalue(body[3]) == 0 then
              return 0
            end
            return process_lvalue(body[2]) % process_lvalue(body[3])
          elseif body[1][2] == "==" then
            return boolToInt(process_lvalue(body[2]) == process_lvalue(body[3]))
          elseif body[1][2] == "!=" then
            return boolToInt(process_lvalue(body[2]) ~= process_lvalue(body[3]))
          elseif body[1][2] == "<" then
            return boolToInt(process_lvalue(body[2]) < process_lvalue(body[3]))
          elseif body[1][2] == "<=" then
            return boolToInt(process_lvalue(body[2]) <= process_lvalue(body[3]))
          elseif body[1][2] == ">" then
            return boolToInt(process_lvalue(body[2]) > process_lvalue(body[3]))
          elseif body[1][2] == ">=" then
            return boolToInt(process_lvalue(body[2]) >= process_lvalue(body[3]))
          elseif body[1][2] == "&&" then
            return boolToInt(numToBool(process_lvalue(body[2])) and numToBool(process_lvalue(body[3])))
          elseif body[1][2] == "||" then
            return boolToInt(numToBool(process_lvalue(body[2])) or numToBool(process_lvalue(body[3])))
          end
        end
      end
    end

    function process_lvalue(value)
      local lvalue, array = eval_expression(value)
      local index
      if array then
        if state.a[lvalue] == nil then
          return 0
        end
        index = eval_expression(value[3])
        if state.a[lvalue][index] == nil then
          return 0
        else
          return state.a[lvalue][index]
        end
      elseif type(lvalue) == "number" then
        return lvalue
      else
        if state.v[lvalue] == nil then
          return 0
        else
          return state.v[lvalue]
        end
      end
    end
    -- Body of function interp
    interp_stmt_list(ast)
    return state
end


-- ***** Module Export *****


return interpit
