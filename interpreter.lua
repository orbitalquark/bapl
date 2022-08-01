local lpeg = require('lpeg')
local pt = require('pt')
local P, S, V = lpeg.P, lpeg.S, lpeg.V
local C, Cc, Cf, Cg, Cmt, Cs, Ct = lpeg.C, lpeg.Cc, lpeg.Cf, lpeg.Cg, lpeg.Cmt, lpeg.Cs, lpeg.Ct
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
  local function field(name, patt) return Cg(patt, name) end
  local function node(tag, patt) return Ct(field('tag', Cc(tag)) * patt) * self._space end
  local function op(patt) return C(patt) * self._space end
  local function reserved(...) return self:_reserved(...) end
  local function binop_node(tag, left, op, right)
    return {tag = tag, left = left, op = op, right = right}
  end
  -- Folded version of node().
  function fnode(tag, patt)
    return Cf(patt, function(left, op, right) return binop_node(tag, left, op, right) end)
  end
  -- Folds an if-elseif-else statement, with elseif being optional.
  -- if {...} elseif {...} is transformed into if {...} else { if {...} }.
  -- Note: an if by itself does not need folding.
  function fold_if(node, new)
    local if_node = node
    while if_node.block_else do if_node = if_node.block_else end
    if new.tag == 'else' then new = new.block end
    if_node.block_else = new
    return node
  end
  -- Folds a switch-case-else statement into if-elseif-else, with case being optional.
  -- switch expr; case x {...} case y {...} is transformed into
  -- if expr == x {...} else { if expr == y {...} }.
  -- Note: a switch by itself does not need folding; it is a no-op.
  function fold_switch(node, new)
    if new.expr then new.expr = binop_node('binop', node.expr, '==', new.expr) end
    if node.body then
      fold_if(node.body, new) -- continue if statement
      return node
    end
    if new.tag == 'else' then new = new.block end
    node.body = new -- either {tag = 'if' ... } or statement(s) from else block
    return node
  end

  self._grammar = P{
    V('reset_pos') * V('stats') * -1,

    -- Whitespace and comments.
    space = (locale.space + V('comment'))^0 * V('save_pos'),
    comment = '#{' * (P(1) - '#}')^0 * '#}' + '#' * (P(1) - '\n')^0,
    -- comment = node('comment', field('text', '#{' * (P(1) - '#}')^0 * '#}' + '#' * (P(1) - '\n')^0)),
    
    -- Basic patterns.
    identifier = C(Cmt((alpha + '_') * (alnum + '_')^0, self:_non_reserved())) * self._space,
    variable = node('variable', field('id', V('identifier'))), --
    hex_num = '0' * S('xX') * xdigit^1,
    dec_num = digit^1 * ('.' * digit^1)^-1 * (S('eE') * S('+-')^-1 * digit^1)^-1,
    number = node('number', field('value', (V('hex_num') + V('dec_num')) / tonumber)),
    int = P('-')^-1 * digit^1 / tonumber, -- for indexes and ranges
    
    -- Strings.
    string = node('string',
      '"' * Cg((V('char_esc') + V('hex_esc') + V('emb_expr') + V('chars')))^0 * '"'),
    char_esc = '\\' * C(S('abfnrtvz"\\`')) /
      setmetatable({a = '\a', b = '\b', f = '\f', n = '\n', r = '\r', t = '\t', v = '\v', z = '\z'},
        {__index = function(_, k) return k end}),
    hex_esc = Cs(P('\\') / '0' * 'x' * xdigit * xdigit) / tonumber / string.char, --
    emb_expr = '`' * V('expr') * '`', --
    chars = (P(1) - S('"\\`'))^1,

    -- Expressions in order of precedence.
    primary = V('postfix') + V('variable') + V('number') + V('string') + V('parens') + V('unary'),
    postfix = V('index'), --
    index = node('index', field('id', V('identifier')) * token('[') *
      (field('start', V('int')^-1) * token(':') * field('end', V('int')^-1) +
        field('value', V('int'))) * token(']')), --
    parens = token('(') * V('expr') * token(')'),
    unary = node('unop', field('op', op(S('-!'))) * field('expr', V('exp'))),
    exp = node('binop',
      field('left', V('primary')) * (field('op', op('^')) * field('right', V('exp'))))^1 +
      V('primary'), -- right-associative, so cannot use fnode('binop', ...)
    mul = fnode('binop', V('exp') * Cg(op(S('*/%')) * V('exp'))^0),
    add = fnode('binop', V('mul') * Cg(op(S('+-')) * V('mul'))^0),
    concat = fnode('binop', V('add') * Cg(op('..') * V('add'))^0),
    cmp = fnode('binop',
      V('concat') * Cg(op(P('>=') + '>' + '<=' + '<' + '==' + '!=') * V('concat'))^0),
    land = fnode('logop', V('cmp') * Cg(op('and') * V('cmp'))^0),
    lor = fnode('logop', V('land') * Cg(op('or') * V('land'))^0), --
    expr = V('lor'),

    -- Statements.
    block = token('{') * (V('stats') + node('empty', token(';')^0)) * token('}'),
    stats = node('seq', field('left', V('stat')) * (token(';')^1 * field('right', V('stats')))) +
      V('stat') * token(';')^-1, --
    stat = V('block') + V('if') + V('switch') + V('while') + V('assign') + V('print') + V('return'),
    ['if'] = Cf(
      node('if', reserved('if') * field('expr', V('expr')) * field('block', V('block'))) *
        (node('if', reserved('elseif') * field('expr', V('expr')) * field('block', V('block'))))^0 *
        (node('else', reserved('else') * field('block', V('block'))))^-1, fold_if),
    switch = Cf(node('switch', reserved('switch') * field('expr', V('expr'))) *
      (node('if', reserved('case') * field('expr', V('expr')) * field('block', V('block'))))^0 *
      (node('else', reserved('else') * field('block', V('block'))))^-1, fold_switch),
    ['while'] = node('while',
      reserved('while') * field('expr', V('expr')) * field('block', V('block'))),
    assign = node('assign', field('id', V('identifier')) * token('=') * field('expr', V('expr'))),
    print = node('print', token('@') * field('expr', V('expr'))),
    ['return'] = node('return', reserved('return') * field('expr', V('expr'))),

    -- Utility.
    reset_pos = P(function()
      self._max_pos = 0
      return true
    end) * self._space, --
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
local CONCAT = 'concat'
local INDEX = 'index'
local SUBSTR = 'substr'

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
-- @param ... Optional values for `op`, such as a number to push or variable to store or load.
function opcodes:_add(op, ...)
  table.insert(self, (assert(op, 'attemp to add nil op')))
  for _, value in ipairs({...}) do if value then table.insert(self, value) end end
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
  return (assert(self.vars[id], 'undefined variable: ' .. id))
end

local bin_opcodes = {
  ['+'] = ADD, ['-'] = SUB, ['*'] = MUL, ['/'] = DIV, ['%'] = MOD, ['^'] = POW, ['>='] = GTE,
  ['>'] = GT, ['<='] = LTE, ['<'] = LT, ['=='] = EQ, ['!='] = NE, ['..'] = CONCAT
}
local un_opcodes = {['-'] = UNM, ['!'] = NOT}
local log_opcodes = {['and'] = JMPZP, ['or'] = JMPNZP}

-- Adds the opcodes for the given expression to the list.
-- @param node Abstract syntax tree node of the expression to add.
function opcodes:_add_expr(node)
  if not self._dispatch_add_expr then
    self._dispatch_add_expr = setmetatable({
      number = function(self, node) self:_add(PUSH, node.value) end,
      variable = function(self, node) self:_add(LOAD, self:_variable_id(node.id)) end,
      binop = function(self, node)
        self:_add_expr(node.left)
        self:_add_expr(node.right)
        self:_add(bin_opcodes[node.op], node.op == '..' and 2)
      end, --
      unop = function(self, node)
        self:_add_expr(node.expr)
        self:_add(un_opcodes[node.op])
      end, --
      logop = function(self, node)
        self:_add_expr(node.left)
        local over_right = self:_jump_start(log_opcodes[node.op])
        self:_add_expr(node.right)
        self:_jump_end(over_right)
      end, --
      string = function(self, node)
        for i, chunk in ipairs(node) do
          if type(chunk) == 'table' then
            self:_add_expr(chunk)
          else
            self:_add(PUSH, chunk)
          end
        end
        if #node > 1 or type(node[1]) ~= 'string' then self:_add(CONCAT, #node) end
      end, --
      index = function(self, node)
        self:_add(LOAD, self:_variable_id(node.id))
        if node.value then
          self:_add(INDEX, node.value)
        else
          if node.start == '' then node.start = 1 end
          if node['end'] == '' then node['end'] = -1 end
          self:_add(SUBSTR, node.start, node['end'])
        end
      end --
    }, {__index = function(_, tag) error('unknown expr tag: ' .. tag) end})
  end
  self._dispatch_add_expr[node.tag](self, node)
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
  if not self._dispatch_add_stat then
    self._dispatch_add_stat = setmetatable({
      assign = function(self, node)
        self:_add_expr(node.expr)
        self:_add(STORE, self:_variable_id(node.id, true))
      end, --
      seq = function(self, node)
        self:_add_stat(node.left)
        self:_add_stat(node.right)
      end, --
      print = function(self, node)
        self:_add_expr(node.expr)
        self:_add(PRINT)
      end, --
      ['return'] = function(self, node)
        self:_add_expr(node.expr)
        self:_add(RET)
      end, --
      ['if'] = function(self, node)
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
      end, --
      ['while'] = function(self, node)
        local to_expr = self:_jump_end()
        self:_add_expr(node.expr)
        local over_while = self:_jump_start(JMPZ)
        self:_add_stat(node.block)
        self:_jump_start(JMP, to_expr)
        self:_jump_end(over_while) -- expr was false
      end, --
      switch = function(self, node) if node.body then self:_add_stat(node.body) end end,
      empty = function() end -- no-op
    }, {__index = function(_, tag) error('unknown stat tag: ' .. node.tag) end})
  end
  self._dispatch_add_stat[node.tag](self, node)
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

-- Stack machine.
local machine = {}

-- Returns a new stack machine.
function machine.new() return setmetatable({}, {__index = machine}) end

local _print = print -- for @ statement so that it is never silenced.

-- Executes the given list of opcodes on this machine and returns the result (the value at the
-- top of the stack).
-- @param opcodes List of opcodes to execute.
-- @see opcodes.new
function machine:run(opcodes)
  print(pt.pt(opcodes))
  if not self._memory then self._memory = {} end
  if not self._stack then self._stack = stack.new() end
  local memory, stack = self._memory, self._stack

  if not self._dispatch then
    self._dispatch = setmetatable({
      [RET] = function() return true end, -- signal completion
      [PUSH] = function()
        local value = opcodes:next()
        print(PUSH, value)
        stack:push(value)
      end, --
      [LOAD] = function()
        local id = opcodes:next()
        print(LOAD, id)
        stack:push(memory[id])
      end, --
      [STORE] = function()
        local id = opcodes:next()
        print(STORE, id)
        memory[id] = stack:pop()
      end, --
      [PRINT] = function()
        local value = stack:pop()
        print(PRINT, value)
        _print(value)
      end, --
      [CONCAT] = function()
        local n = opcodes:next()
        print(CONCAT, n)
        if n > 1 then
          local chunks = {}
          for i = 1, n do table.insert(chunks, 1, stack:pop()) end
          stack:push(table.concat(chunks))
        elseif type(stack:top()) ~= 'string' then
          stack:push(tostring(stack:pop()))
        end
      end, --
      [INDEX] = function()
        local i = opcodes:next()
        print(INDEX, i)
        local value, value_type = self:_assert_indexible(stack:pop())
        if value_type == 'string' then stack:push(string.sub(value, i, i)) end
      end, --
      [SUBSTR] = function()
        local s, e = opcodes:next(), opcodes:next()
        print(SUBSTR, s, e)
        local value, value_type = self:_assert_indexible(stack:pop())
        if value_type == 'string' then stack:push(string.sub(value, s, e)) end
      end --
    }, {{__index = function(_, opcode) error('unknown instruction: ' .. opcode) end}})

    for opcode, f in pairs{
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
    } do
      self._dispatch[opcode] = function()
        local right, left = stack:pop(), stack:pop()
        print(opcode, left, right)
        stack:push(f(left, right))
      end
    end

    for opcode, f in pairs{
      [UNM] = function(a) return -a end, --
      [NOT] = function(a) return a == 0 and 1 or 0 end --
    } do
      self._dispatch[opcode] = function()
        local value = stack:pop()
        print(opcode, value)
        stack:push(f(value))
      end
    end

    for opcode in pairs{[JMP] = true, [JMPZ] = true, [JMPZP] = true, [JMPNZP] = true} do
      self._dispatch[opcode] = function()
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
      end
    end
  end

  while true do if self._dispatch[opcodes:next()]() then break end end

  return stack:pop()
end

-- Asserts the given value is of an indexible type and returns that value and its type.
function machine:_assert_indexible(value)
  local value_type = type(value)
  if value_type ~= 'string' then error(string.format('cannot index %s value', value_type)) end
  return value, value_type
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
