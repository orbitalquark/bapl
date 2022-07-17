local lpeg = require('lpeg')
local pt = require('pt')
local P, S, R, V = lpeg.P, lpeg.S, lpeg.R, lpeg.V
local C, Ct = lpeg.C, lpeg.Ct

-- ===============================================================================================--
-- Parser.

local function node_var(id) return {tag = 'variable', value = id} end
local function node_num(num) return {tag = 'number', value = tonumber(num)} end
local function node_assign(id, expr) return {tag = 'assign', id = id, expr = expr} end
local function node_seq(left, right)
  if not right then return left end
  return {tag = 'seq', left = left, right = right}
end
local function node_print(expr) return {tag = 'print', expr = expr} end
local function node_return(expr) return {tag = 'return', expr = expr} end

local space = S(' \t\r\n')^0

local identifier = C((R('az') + '_') * (R('az', 'AZ', '09') + '_')^0) * space
local variable = identifier / node_var

local hex_num = '0' * S('xX') * R('09', 'AF', 'af')^1
local digits = R('09')^1
local dec_num = digits * ('.' * digits)^-1 * (S('eE') * S('+-')^-1 * digits)^-1
local numeral = (hex_num + dec_num) / node_num * space

local lparen = '(' * space
local rparen = ')' * space
local lbrace = '{' * space
local rbrace = '}' * space
local equals = '=' * space
local semicolon = ';' * space
local at = '@' * space

local ret = 'return' * space

local op_add = C(S('+-')) * space
local op_mul = C(S('*/%')) * space
local op_exp = C(S('^')) * space
local op_un = C(S('-')) * space
local op_cmp = C(P('>=') + '>' + '<=' + '<' + '==' + '!=') * space

local function fold_binop(list)
  local tree = list[1]
  for i = 2, #list, 2 do tree = {tag = 'binop', left = tree, op = list[i], right = list[i + 1]} end
  return tree
end

local function fold_binop_rassoc(list)
  local tree = list[#list]
  for i = #list - 1, 2, -2 do
    tree = {tag = 'binop', right = tree, op = list[i], left = list[i - 1]}
  end
  return tree
end

local function fold_unop(list) return {tag = 'unop', op = list[1], left = list[2]} end

local grammar = space * P{
  'stats',
  --
  stats = V('stat') * (semicolon^1 * V('stats'))^-1 / node_seq,
  block = lbrace * V('stats') * semicolon^-1 * rbrace,
  stat = V('block') + V('assign') + V('print') + V('return'),
  assign = identifier * equals * V('expr') / node_assign, --
  print = at * V('expr') / node_print, --
  ['return'] = ret * V('expr') / node_return,
  --
  primary = variable + numeral + lparen * V('expr') * rparen + V('unary'),
  unary = Ct(op_un * V('exp')) / fold_unop,
  exp = Ct(V('primary') * (op_exp * V('primary'))^0) / fold_binop_rassoc,
  mul = Ct(V('exp') * (op_mul * V('exp'))^0) / fold_binop,
  add = Ct(V('mul') * (op_add * V('mul'))^0) / fold_binop,
  cmp = Ct(V('add') * (op_cmp * V('add'))^0) / fold_binop, --
  expr = V('cmp')
} * -1

-- Parses the given input and returns the resulting Abstract Syntax Tree.
-- @param input String input to parse.
local function parse(input) return grammar:match(input) end

-- ===============================================================================================--
-- Compiler.

-- List of opcodes for a stack machine.
local opcodes = {}

-- Creates a new list of opcodes.
function opcodes.new() return setmetatable({}, {__index = opcodes}) end

-- Adds the given opcode and optional value to the list.
-- @param op Opcode to add.
-- @param value Optional value for `op`, such as a number to push or variable to store or load.
function opcodes:add(op, value)
  table.insert(self, op)
  if value then table.insert(self, value) end
end

-- Returns a numeric ID for the given variable, creating it if possible.
-- @param id Variable to fetch an ID for.
-- @param can_create Flag that indicates whether or not an ID can be created. If `false` and
--  there is no numeric ID is available, raises an error for the undefined variable.
function opcodes:variable_id(id, can_create)
  if not self.vars then self.vars = {} end
  if not self.vars[id] and can_create then
    table.insert(self.vars, id)
    self.vars[id] = #self.vars
  end
  return assert(self.vars[id], 'undefined variable: ' .. id)
end

local binops = {
  ['+'] = 'add', ['-'] = 'sub', ['*'] = 'mul', ['/'] = 'div', ['%'] = 'mod', ['^'] = 'pow',
  ['>='] = 'gte', ['>'] = 'gt', ['<='] = 'lte', ['<'] = 'lt', ['=='] = 'eq', ['!='] = 'ne'
}
local unops = {['-'] = 'unm'}

-- Adds the opcodes for the given expression to the list.
-- @param ast Abstract syntax tree of the expression to add.
function opcodes:add_expr(ast)
  if ast.tag == 'number' then
    self:add('push', ast.value)
  elseif ast.tag == 'variable' then
    self:add('load', self:variable_id(ast.value))
  elseif ast.tag == 'binop' then
    self:add_expr(ast.left)
    self:add_expr(ast.right)
    self:add(binops[ast.op])
  elseif ast.tag == 'unop' then
    self:add_expr(ast.left)
    self:add(unops[ast.op])
  else
    error('invalid tree')
  end
end

-- Adds the opcodes for the given statement to the list.
-- @param ast Abstract syntax tree of the statement to add.
function opcodes:add_stat(ast)
  if ast.tag == 'assign' then
    self:add_expr(ast.expr)
    self:add('store', self:variable_id(ast.id, true))
  elseif ast.tag == 'seq' then
    self:add_stat(ast.left)
    self:add_stat(ast.right)
  elseif ast.tag == 'print' then
    self:add_expr(ast.expr)
    self:add('print')
  elseif ast.tag == 'return' then
    self:add_expr(ast.expr)
    self:add('ret')
  else
    error('invalid tree')
  end
end

-- Returns the next opcode or value in the list.
function opcodes:next()
  if not self.i then self.i = 0 end
  self.i = self.i + 1
  return self[self.i]
end

-- Compiles the given Abstract Syntax Tree into a list of opcodes and returns them.
-- @param ast Abstract syntax tree to compile.
-- @see parse
local function compile(ast)
  local opcodes = opcodes.new()
  opcodes:add_stat(ast)
  -- Add implicit 'return 0' statement
  opcodes:add('push', 0)
  opcodes:add('ret')
  return opcodes
end

-- ===============================================================================================--
-- Interpreter.

-- A simple stack.
-- Wraps a table with push and pop operations.
local stack = {}
function stack.new() return setmetatable({}, {__index = stack}) end
function stack:push(value) table.insert(self, value) end
function stack:pop() return table.remove(self) end

local bin_ops = {
  add = function(a, b) return a + b end, --
  sub = function(a, b) return a - b end, --
  mul = function(a, b) return a * b end, --
  div = function(a, b) return a / b end, --
  mod = function(a, b) return a % b end, --
  pow = function(a, b) return a^b end, --
  gte = function(a, b) return a >= b and 1 or 0 end, --
  gt = function(a, b) return a > b and 1 or 0 end, --
  lte = function(a, b) return a <= b and 1 or 0 end, --
  lt = function(a, b) return a < b and 1 or 0 end, --
  eq = function(a, b) return a == b and 1 or 0 end, --
  ne = function(a, b) return a ~= b and 1 or 0 end --
}

local un_ops = {
  unm = function(a) return -a end --
}

local _print = print -- for @ statement so that it is never silenced.

-- Stack machine.
local machine = {}

-- Returns a new stack machine.
function machine.new() return setmetatable({}, {__index = machine}) end

-- Executes the given list of opcodes on this machine.
function machine:run(opcodes)
  if not self.memory then self.memory = {} end
  if not self.stack then self.stack = stack.new() end
  local memory, stack = self.memory, self.stack
  while true do
    local opcode = opcodes:next()
    if opcode == 'ret' then
      return
    elseif opcode == 'push' then
      local value = opcodes:next()
      print('push', value)
      stack:push(value)
    elseif bin_ops[opcode] then
      local right, left = stack:pop(), stack:pop()
      print(opcode, left, right)
      stack:push(bin_ops[opcode](left, right))
    elseif un_ops[opcode] then
      local value = stack:pop()
      print(opcode, value)
      stack:push(un_ops[opcode](value))
    elseif opcode == 'load' then
      local id = opcodes:next()
      print('load', id)
      stack:push(memory[id])
    elseif opcode == 'store' then
      local id = opcodes:next()
      print('store', id)
      memory[id] = stack:pop()
    elseif opcode == 'print' then
      local value = stack:pop()
      print('print', value)
      _print(value)
    else
      error('unknown instruction: ' .. opcode)
    end
  end
end

-- Executes the given list of opcodes on a new stack machine and returns the result (the value at
-- the top of the stack).
-- @param opcodes List of opcodes to execute.
-- @see compile
local function run(opcodes)
  local instance = machine.new()
  instance:run(opcodes)
  return instance.stack:pop()
end

-- ===============================================================================================--
-- Module.

-- Interpreter module.
-- @field verbose Whether or not print debug info when running. Debug info includes the Abstract
--   Syntax Tree and opcodes.
local M = {verbose = false}

-- Runs the given input code and returns its result.
-- @param input Input code to run.
function M.run(input)
  local _print = print
  print = function(...) if M.verbose then _print(...) end end

  print(input)
  local ast = parse(input)
  print(pt.pt(ast))
  local opcodes = compile(ast)
  local result = run(opcodes)

  print = _print -- restore
  return result
end

return M
