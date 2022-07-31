local lpeg = require('lpeg')
local pt = require('pt')
local P, S, V = lpeg.P, lpeg.S, lpeg.V
local C, Cc, Cf, Cg, Cmt, Ct = lpeg.C, lpeg.Cc, lpeg.Cf, lpeg.Cg, lpeg.Cmt, lpeg.Ct
local locale = lpeg.locale()
local alpha, alnum, digit, xdigit = locale.alpha, locale.alnum, locale.digit, locale.xdigit

-- ===============================================================================================--
-- Parser.

-- Language grammar.
local grammar = {}

---
-- Creates a new language grammar.
-- @usage ast = grammar.new():parse(input)
function grammar.new() return setmetatable({}, {__index = grammar}) end

-- Initializes the grammar pattern.
function grammar:_init()
  self._space = V('space')
  -- Convenience functions.
  local function token(char) return char * self._space end
  local function node(tag, patt) return Ct(Cg(Cc(tag), 'tag') * patt) * self._space end
  local function reserved(...) return self:_reserved(...) end
  local function binop(patt) return Cg(C(patt), 'op') * self._space end
  local function opnode(tag, left, op, right)
    return {tag = tag, left = left, op = op, right = right}
  end
  -- Folds an if-elseif-else statement, with elseif being optional.
  -- if {...} elseif {...} is transformed into if {...} else { if {...} }.
  -- Note: an if by itself does not need folding.
  function fold_if(tree, new)
    local node = tree
    while node.block_else do node = node.block_else end
    if new.tag == 'else' then new = new.block end
    node.block_else = new
    return tree
  end
  -- Folds a switch-case-else statement into if-elseif-else, with case being optional.
  -- switch expr; case x {...} case y {...} is transformed into
  -- if expr == x {...} else { if expr == y {...} }.
  -- Note: a switch by itself does not need folding; it is a no-op.
  function fold_switch(tree, new)
    if new.expr then new.expr = opnode('binop', tree.expr, '==', new.expr) end
    if tree.body then
      fold_if(tree.body, new) -- continue if statement
      return tree
    end
    if new.tag == 'else' then new = new.block end
    tree.body = new -- either {tag = 'if' ... } or statement(s) from else block
    return tree
  end
  -- Folds a left-associative binary operator.
  function fold_binop(tree, new) return opnode('binop', tree, new.op, new.right) end
  -- Folds a right-associative list of binary operations.
  function fold_binop_rassoc(list)
    local tree = list[#list]
    for i = #list - 1, 2, -2 do tree = opnode('binop', list[i - 1], list[i], tree) end
    return tree
  end
  -- Folds a left-associative logical operator.
  function fold_logop(tree, new) return opnode('logop', tree, new.op, new.right) end

  self._grammar = P{
    V('reset_pos') * self._space * V('stats') * -1,

    -- Whitespace and comments.
    space = (locale.space + V('comment'))^0 * V('save_pos'),
    comment = '#{' * (P(1) - '#}')^0 * '#}' + '#' * (P(1) - '\n')^0,
    -- comment = node('comment', Cg('#{' * (P(1) - '#}')^0 * '#}' + '#' * (P(1) - '\n')^0, 'text')),
    
    -- Basic patterns.
    identifier = Cg(Cmt((alpha + '_') * (alnum + '_')^0, self:_non_reserved()), 'id') * self._space,
    variable = node('variable', V('identifier')), --
    hex_num = '0' * S('xX') * xdigit^1,
    dec_num = digit^1 * ('.' * digit^1)^-1 * (S('eE') * S('+-')^-1 * digit^1)^-1,
    numeral = node('number', Cg((V('hex_num') + V('dec_num')) / tonumber, 'value')),

    -- Statements.
    block = token('{') * (V('stats') + node('empty', token(';')^0)) * token('}'),
    stats = node('seq', Cg(V('stat'), 'left') * (token(';')^1 * Cg(V('stats'), 'right'))) +
      V('stat') * token(';')^-1, --
    stat = V('block') + V('if') + V('switch') + V('while') + V('assign') + V('print') + V('return'),
    ['if'] = Cf(node('if', reserved('if') * Cg(V('expr'), 'expr') * Cg(V('block'), 'block')) *
      (node('if', reserved('elseif') * Cg(V('expr'), 'expr') * Cg(V('block'), 'block')))^0 *
      (node('else', reserved('else') * Cg(V('block'), 'block')))^-1, fold_if),
    switch = Cf(node('switch', reserved('switch') * Cg(V('expr'), 'expr')) *
      (node('if', reserved('case') * Cg(V('expr'), 'expr') * Cg(V('block'), 'block')))^0 *
      (node('else', reserved('else') * Cg(V('block'), 'block')))^-1, fold_switch),
    ['while'] = node('while', reserved('while') * Cg(V('expr'), 'expr') * Cg(V('block'), 'block')),
    assign = node('assign', V('identifier') * token('=') * Cg(V('expr'), 'expr')),
    print = node('print', token('@') * Cg(V('expr'), 'expr')),
    ['return'] = node('return', reserved('return') * Cg(V('expr'), 'expr')),

    -- Expressions in order of precedence.
    primary = V('variable') + V('numeral') + token('(') * V('expr') * token(')') + V('unary'),
    unary = node('unop', binop(S('-!')) * Cg(V('exp'), 'expr')),
    exp = Ct(V('primary') * (C(S('^')) * self._space * V('primary'))^0) / fold_binop_rassoc,
    mul = Cf(V('exp') * Ct(binop(S('*/%')) * Cg(V('exp'), 'right'))^0, fold_binop),
    add = Cf(V('mul') * Ct(binop(S('+-')) * Cg(V('mul'), 'right'))^0, fold_binop),
    cmp = Cf(
      V('add') * Ct(binop(P('>=') + '>' + '<=' + '<' + '==' + '!=') * Cg(V('add'), 'right'))^0,
      fold_binop), --
    land = Cf(V('cmp') * Ct(binop('and') * Cg(V('cmp'), 'right'))^0, fold_logop),
    lor = Cf(V('land') * Ct(binop('or') * Cg(V('land'), 'right'))^0, fold_logop), --
    expr = V('lor'),

    -- Utility.
    reset_pos = P(function()
      self._max_pos = 0
      return true
    end), --
    save_pos = P(function(_, i)
      self._max_pos = math.max(self._max_pos, i)
      return true
    end)
  }
end

-- Reserves the given word and returns a pattern that matches it.
-- This is to be used when constructing the grammar in `_init()`.
-- @param word Word to reserve and return a matching pattern for.
-- @see _init
function grammar:_reserved(word)
  if not self._reserved_words then self._reserved_words = {} end
  self._reserved_words[word] = true
  return word * -alnum * self._space
end

-- Returns a function that validates a captured word as non-reserved.
-- This is to be used in conjunction with `lpeg.Cmt()` when constructing the grammar in `_init()`.
-- @see _init
function grammar:_non_reserved()
  return function(_, _, word)
    if self._reserved_words[word] then return false end
    return true, word
  end
end

---
-- Parses the given input and returns the resulting Abstract Syntax Tree.
-- Raises an error if a syntax error was encountered.
-- @param input String input to parse.
function grammar:parse(input)
  if not self._grammar then self:_init() end
  local ast = self._grammar:match(input)
  if not ast then
    local parsed = input:sub(1, self._max_pos - 1)
    if parsed:find('\n$') then parsed = parsed:sub(1, -2) end -- chomp
    local line = select(2, parsed:gsub('\n', '\n')) + 1
    local s, e = parsed:find('[^\n]*$')
    local col = e - s + 2 -- blame col of next char
    error(string.format('syntax error at line %d, col %d', line, col))
  end
  return ast
end

-- ===============================================================================================--
-- Compiler.

-- Opcodes.
local RET = 'ret'
local PUSH = 'push'
local ADD = 'add'
local SUB = 'sub'
local MUL = 'mul'
local DIV = 'div'
local MOD = 'mod'
local POW = 'pow'
local GTE = 'gte'
local GT = 'gt'
local LTE = 'lte'
local LT = 'lt'
local EQ = 'eq'
local NE = 'ne'
local UNM = 'unm'
local NOT = 'not'
local LOAD = 'load'
local STORE = 'store'
local PRINT = 'print'
local JMP = 'jmp'
local JMPZ = 'jmpz'
local JMPZP = 'jmpzp'
local JMPNZP = 'jmpnzp'

-- List of opcodes for a stack machine.
local opcodes = {}

---
-- Creates a list of opcodes from the given Abstract syntax tree.
-- @param ast Abstract syntax tree to compile.
-- @see grammar.parse
function opcodes.new(ast)
  local codes = setmetatable({}, {__index = opcodes})
  codes:_add_stat(ast)
  -- Add implicit 'return 0' statement
  codes:_add(PUSH, 0)
  codes:_add(RET)
  return codes
end

-- Adds the given opcode and optional value to the list.
-- @param op Opcode to add.
-- @param value Optional value for `op`, such as a number to push or variable to store or load.
function opcodes:_add(op, value)
  table.insert(self, (assert(op, 'attemp to add nil op')))
  if value then table.insert(self, value) end
end

-- Returns a numeric ID for the given variable, creating it if possible.
-- @param id Variable to fetch an ID for.
-- @param can_create Flag that indicates whether or not an ID can be created. If `false` and
--  there is no numeric ID is available, raises an error for the undefined variable.
function opcodes:_variable_id(id, can_create)
  if not self.vars then self.vars = {} end
  if not self.vars[id] and can_create then
    table.insert(self.vars, id)
    self.vars[id] = #self.vars
  end
  return assert(self.vars[id], 'undefined variable: ' .. id)
end

local bin_opcodes = {
  ['+'] = ADD, ['-'] = SUB, ['*'] = MUL, ['/'] = DIV, ['%'] = MOD, ['^'] = POW, ['>='] = GTE,
  ['>'] = GT, ['<='] = LTE, ['<'] = LT, ['=='] = EQ, ['!='] = NE
}
local un_opcodes = {['-'] = UNM, ['!'] = NOT}
local log_opcodes = {['and'] = JMPZP, ['or'] = JMPNZP}

-- Adds the opcodes for the given expression to the list.
-- @param node Abstract syntax tree node of the expression to add.
function opcodes:_add_expr(node)
  if node.tag == 'number' then
    self:_add(PUSH, node.value)
  elseif node.tag == 'variable' then
    self:_add(LOAD, self:_variable_id(node.id))
  elseif node.tag == 'binop' then
    self:_add_expr(node.left)
    self:_add_expr(node.right)
    self:_add(bin_opcodes[node.op])
  elseif node.tag == 'unop' then
    self:_add_expr(node.expr)
    self:_add(un_opcodes[node.op])
  elseif node.tag == 'logop' then
    self:_add_expr(node.left)
    local over_right = self:_jump_start(log_opcodes[node.op])
    self:_add_expr(node.right)
    self:_jump_end(over_right)
  else
    error('unknown expr tag: ' .. tag)
  end
end

-- Starts a forward jump or completes a backward jump.
-- @param op Jump opcode.
-- @param id Optional id, returned by `_jump_end()`, for a backward jump.
-- @see _jump_end
-- @return id of the jump to pass to `_jump_end()` for a forward jump
function opcodes:_jump_start(op, id)
  self:_add(op, not id and 0 or id - #self - 2) -- extra -2 for this instruction
  if not id then return #self end
end

-- Ends a forward jump or starts a backward jump.
-- @param id Optional id, returned by `_jump_start()`, for a forward jump.
-- @see _jump_start
-- @return id of the jump to pass to `_jump_start()` for a backward jump
function opcodes:_jump_end(id)
  if not id then return #self end
  self[id] = #self - id
end

-- Adds the opcodes for the given statement to the list.
-- @param node Abstract syntax tree node of the statement to add.
function opcodes:_add_stat(node)
  if node.tag == 'assign' then
    self:_add_expr(node.expr)
    self:_add(STORE, self:_variable_id(node.id, true))
  elseif node.tag == 'seq' then
    self:_add_stat(node.left)
    self:_add_stat(node.right)
  elseif node.tag == 'print' then
    self:_add_expr(node.expr)
    self:_add(PRINT)
  elseif node.tag == 'return' then
    self:_add_expr(node.expr)
    self:_add(RET)
  elseif node.tag == 'if' then
    self:_add_expr(node.expr)
    local over_if = self:_jump_start(JMPZ)
    self:_add_stat(node.block)
    if not node.block_else then
      self:_jump_end(over_if) -- expr was false
    else
      local over_else = self:_jump_start(JMP)
      self:_jump_end(over_if) -- jump into else block (expr was false)
      self:_add_stat(node.block_else)
      self:_jump_end(over_else) -- expr was true
    end
  elseif node.tag == 'while' then
    local to_expr = self:_jump_end()
    self:_add_expr(node.expr)
    local over_while = self:_jump_start(JMPZ)
    self:_add_stat(node.block)
    self:_jump_start(JMP, to_expr)
    self:_jump_end(over_while) -- expr was false
  elseif node.tag == 'switch' then
    if node.body then self:_add_stat(node.body) end
  elseif node.tag == 'empty' then -- no-op
  else
    error('unknown stat tag: ' .. node.tag)
  end
end

---
-- Returns the next opcode or value in the list.
function opcodes:next()
  if not self.i then self.i = 0 end
  self.i = self.i + 1
  return self[self.i]
end

---
-- Jumps to a relative opcode position in the list.
-- @param rel Opcode position to jump to, relative to the current position.
function opcodes:jump(rel) self.i = self.i + rel end

-- ===============================================================================================--
-- Interpreter.

-- A simple stack.
-- Wraps a table with push and pop operations.
local stack = {}
function stack.new() return setmetatable({}, {__index = stack}) end
function stack:push(value) table.insert(self, value) end
function stack:top() return self[#self] end
function stack:pop() return table.remove(self) end

local bin_ops = {
  [ADD] = function(a, b) return a + b end, --
  [SUB] = function(a, b) return a - b end, --
  [MUL] = function(a, b) return a * b end, --
  [DIV] = function(a, b) return a / b end, --
  [MOD] = function(a, b) return a % b end, --
  [POW] = function(a, b) return a^b end, --
  [GTE] = function(a, b) return a >= b and 1 or 0 end, --
  [GT] = function(a, b) return a > b and 1 or 0 end, --
  [LTE] = function(a, b) return a <= b and 1 or 0 end, --
  [LT] = function(a, b) return a < b and 1 or 0 end, --
  [EQ] = function(a, b) return a == b and 1 or 0 end, --
  [NE] = function(a, b) return a ~= b and 1 or 0 end --
}

local un_ops = {
  [UNM] = function(a) return -a end, --
  [NOT] = function(a) return a == 0 and 1 or 0 end
}

local jump_ops = {[JMP] = true, [JMPZ] = true, [JMPZP] = true, [JMPNZP] = true}

local _print = print -- for @ statement so that it is never silenced.

-- Stack machine.
local machine = {}

-- Returns a new stack machine.
function machine.new() return setmetatable({}, {__index = machine}) end

-- Executes the given list of opcodes on this machine and returns the result (the value at the
-- top of the stack).
-- @param opcodes List of opcodes to execute.
-- @see opcodes.new
function machine:run(opcodes)
  print(pt.pt(opcodes))
  if not self._memory then self._memory = {} end
  if not self._stack then self._stack = stack.new() end
  local memory, stack = self._memory, self._stack
  while true do
    local opcode = opcodes:next()
    if opcode == RET then
      break
    elseif opcode == PUSH then
      local value = opcodes:next()
      print(opcode, value)
      stack:push(value)
    elseif bin_ops[opcode] then
      local right, left = stack:pop(), stack:pop()
      print(opcode, left, right)
      stack:push(bin_ops[opcode](left, right))
    elseif un_ops[opcode] then
      local value = stack:pop()
      print(opcode, value)
      stack:push(un_ops[opcode](value))
    elseif opcode == LOAD then
      local id = opcodes:next()
      print(opcode, id)
      stack:push(memory[id])
    elseif opcode == STORE then
      local id = opcodes:next()
      print(opcode, id)
      memory[id] = stack:pop()
    elseif opcode == PRINT then
      local value = stack:pop()
      print(opcode, value)
      _print(value)
    elseif jump_ops[opcode] then
      local rel = opcodes:next()
      print(opcode, rel)
      local zero = stack:top() == 0
      local jump = opcode == JMP or ((opcode == JMPZ or opcode == JMPZP) and zero) or
        (opcode == JMPNZP and not zero)
      local pop = opcode == JMPZ or (opcode == JMPZP and not zero) or (opcode == JMPNZP and zero)
      if jump then opcodes:jump(rel) end
      if pop then
        print('pop') -- not an opcode, but verify pop op
        stack:pop()
      end
    else
      error('unknown instruction: ' .. opcode)
    end
  end
  return stack:pop()
end

-- ===============================================================================================--
-- Module.

-- Interpreter module.
local M = {grammar = grammar.new()}

-- Runs the given input code and returns its result.
-- @param input Input code to run.
-- @param verbose Optional flag that indicates whether or not print debug info when running. Debug
--   info includes the Abstract Syntax Tree and opcodes.
function M.run(input, verbose)
  local _print = print
  print = function(...) if verbose then _print(...) end end

  print(input)
  local ok, result = pcall(function()
    local ast = M.grammar:parse(input)
    print(pt.pt(ast))
    return machine.new():run(opcodes.new(ast))
  end)

  print = _print -- restore
  return assert(ok and result, result)
end

return M
