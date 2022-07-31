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
  local function op(patt) return Cg(C(patt), 'op') * self._space end
  local function opnode(tag, left, op, right)
    return {tag = tag, left = left, op = op, right = right}
  end
  -- Folds an if-elseif-else statement, with elseif being optional.
  -- if {...} elseif {...} is transformed into if {...} else { if {...} }.
  -- Note: an if by itself does not need folding.
  function fold_if(tree, new)
    local node = tree
    while node.block_else do node = node.block_else end
    node.block_else = new.tag == 'if' and new or new.block
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
    stats = node('seq', Cg(V('stat'), 'left') * (token(';')^1 * Cg(V('stats'), 'right'))) +
      V('stat'), --
    block = token('{') * V('stats') * token(';')^-1 * token('}'),
    stat = V('block') + V('if') + V('while') + V('assign') + V('print') + V('return'),
    ['if'] = Cf(node('if', reserved('if') * Cg(V('expr'), 'cond') * Cg(V('block'), 'block')) *
      (node('if', reserved('elseif') * Cg(V('expr'), 'cond') * Cg(V('block'), 'block')))^0 *
      (node('else', reserved('else') * Cg(V('block'), 'block')))^-1, fold_if),
    ['while'] = node('while', reserved('while') * Cg(V('expr'), 'cond') * Cg(V('block'), 'block')),
    assign = node('assign', V('identifier') * token('=') * Cg(V('expr'), 'expr')),
    print = node('print', token('@') * Cg(V('expr'), 'expr')),
    ['return'] = node('return', reserved('return') * Cg(V('expr'), 'expr')),

    -- Operators.
    op_exp = C(S('^')) * self._space,

    -- Expressions in order of precedence.
    primary = V('variable') + V('numeral') + token('(') * V('expr') * token(')') + V('unary'),
    unary = node('unop', op(S('-!')) * Cg(V('exp'), 'left')),
    exp = Ct(V('primary') * (V('op_exp') * V('primary'))^0) / fold_binop_rassoc,
    mul = Cf(V('exp') * Ct(op(S('*/%')) * Cg(V('exp'), 'right'))^0, fold_binop),
    add = Cf(V('mul') * Ct(op(S('+-')) * Cg(V('mul'), 'right'))^0, fold_binop),
    cmp = Cf(V('add') * Ct(op(P('>=') + '>' + '<=' + '<' + '==' + '!=') * Cg(V('add'), 'right'))^0,
      fold_binop), --
    land = Cf(V('cmp') * Ct(op('and') * Cg(V('cmp'), 'right'))^0, fold_logop),
    lor = Cf(V('land') * Ct(op('or') * Cg(V('land'), 'right'))^0, fold_logop), --
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
  codes:_add('push', 0)
  codes:_add('ret')
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
  ['+'] = 'add', ['-'] = 'sub', ['*'] = 'mul', ['/'] = 'div', ['%'] = 'mod', ['^'] = 'pow',
  ['>='] = 'gte', ['>'] = 'gt', ['<='] = 'lte', ['<'] = 'lt', ['=='] = 'eq', ['!='] = 'ne'
}
local un_opcodes = {['-'] = 'unm', ['!'] = 'not'}
local log_opcodes = {['and'] = 'jmpzp', ['or'] = 'jmpnzp'}

-- Adds the opcodes for the given expression to the list.
-- @param node Abstract syntax tree node of the expression to add.
function opcodes:_add_expr(node)
  if node.tag == 'number' then
    self:_add('push', node.value)
  elseif node.tag == 'variable' then
    self:_add('load', self:_variable_id(node.id))
  elseif node.tag == 'binop' then
    self:_add_expr(node.left)
    self:_add_expr(node.right)
    self:_add(bin_opcodes[node.op])
  elseif node.tag == 'unop' then
    self:_add_expr(node.left)
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
  self:_add(op, not id and 0 or id - #self - 2) -- TODO: why -2?
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
    self:_add('store', self:_variable_id(node.id, true))
  elseif node.tag == 'seq' then
    self:_add_stat(node.left)
    self:_add_stat(node.right)
  elseif node.tag == 'print' then
    self:_add_expr(node.expr)
    self:_add('print')
  elseif node.tag == 'return' then
    self:_add_expr(node.expr)
    self:_add('ret')
  elseif node.tag == 'if' then
    self:_add_expr(node.cond)
    local over_if = self:_jump_start('jmpz')
    self:_add_stat(node.block)
    if not node.block_else then
      self:_jump_end(over_if) -- cond was false
    else
      local over_else = self:_jump_start('jmp')
      self:_jump_end(over_if) -- jump into else block (cond was false)
      self:_add_stat(node.block_else)
      self:_jump_end(over_else) -- cond was true
    end
  elseif node.tag == 'while' then
    local to_cond = self:_jump_end()
    self:_add_expr(node.cond)
    local over_while = self:_jump_start('jmpz')
    self:_add_stat(node.block)
    self:_jump_start('jmp', to_cond)
    self:_jump_end(over_while) -- cond was false
  else
    error('unknown stat tag: ' .. tag)
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
function opcodes:jump(rel)
  self.i = self.i + rel
  assert(self.i > 0 and self.i <= self.i, 'invalid jump: ' .. rel)
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
  unm = function(a) return -a end, --
  ['not'] = function(a) return a == 1 and 0 or 1 end
}

local jump_ops = {jmp = true, jmpz = true, jmpzp = true, jmpnzp = true}

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
    if opcode == 'ret' then
      break
    elseif opcode == 'push' then
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
    elseif opcode == 'load' then
      local id = opcodes:next()
      print(opcode, id)
      stack:push(memory[id])
    elseif opcode == 'store' then
      local id = opcodes:next()
      print(opcode, id)
      memory[id] = stack:pop()
    elseif opcode == 'print' then
      local value = stack:pop()
      print(opcode, value)
      _print(value)
    elseif jump_ops[opcode] then
      local rel = opcodes:next()
      print(opcode, rel)
      local zero = stack[#stack] == 0
      local jump = opcode == 'jmp' or ((opcode == 'jmpz' or opcode == 'jmpzp') and zero) or
        (opcode == 'jmpnzp' and not zero)
      local pop = opcode == 'jmpz' or (opcode == 'jmpzp' and not zero) or
        (opcode == 'jmpnzp' and zero)
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
