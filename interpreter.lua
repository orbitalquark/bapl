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

---
-- Parses the given input and returns the resulting Abstract Syntax Tree.
-- Raises an error if a syntax error was encountered.
-- @param input String input to parse.
function grammar:parse(input)
  if not self._grammar then
    local space = V('space')
    local reserved_words = {}
    -- Convenience functions.
    local function token(char) return char * space end
    local function field(name, patt) return Cg(patt, name) end
    local function node(tag, patt) return Ct(field('tag', Cc(tag)) * patt) * space end
    local function op(patt) return C(patt) * space end
    local function reserved(word)
      reserved_words[word] = true
      return word * -alnum * space
    end
    local function binop_node(tag, left, op, right)
      return {tag = tag, left = left, op = op, right = right}
    end
    local function index_node(tag, variable, expr, expr2)
      return {tag = tag, variable = variable, expr = expr, expr2 = expr2}
    end
    -- Folded version of node().
    function fnode(tag, patt)
      return Cf(patt, function(...)
        return tag:find('op$') and binop_node(tag, ...) or index_node(tag, ...)
      end)
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
      if not node.if_node then
        if new.tag == 'else' then new = new.block end
        node.if_node = new -- either a new if node or statement(s) from else/default block
      else
        fold_if(node.if_node, new) -- continue adding cases to if statement
      end
      return node
    end

    self._grammar = P{
      V('reset_pos') * V('stats') * -1,

      -- Whitespace and comments.
      space = (locale.space + V('comment'))^0 * V('save_pos'),
      comment = '#{' * (P(1) - '#}')^0 * '#}' + '#' * (P(1) - '\n')^0,

      -- Basic patterns.
      identifier = C(Cmt((alpha + '_') * (alnum + '_')^0, function(_, _, word)
        if reserved_words[word] then return false end
        return true, word
      end)) * space, --
      variable = node('variable', field('id', V('identifier'))), --
      hex_num = '0' * S('xX') * xdigit^1,
      dec_num = digit^1 * ('.' * digit^1)^-1 * (S('eE') * S('+-')^-1 * digit^1)^-1,
      number = node('number', field('value', (V('hex_num') + V('dec_num')) / tonumber)),

      -- Strings.
      string = node('string',
        '"' * Cg(V('escape') + V('hex_char') + V('interpolated') + V('chars'))^0 * '"'),
      escape = '\\' * C(S('abfnrtvz"\\`')) /
        setmetatable({
          a = '\a', b = '\b', f = '\f', n = '\n', r = '\r', t = '\t', v = '\v', z = '\z'
        }, {__index = function(_, k) return k end}),
      hex_char = Cs(P('\\') / '0' * 'x' * xdigit * xdigit) / tonumber / string.char,
      interpolated = '`' * V('expr') * '`', --
      chars = (P(1) - S('"\\`'))^1,

      -- Expressions in order of precedence.
      primary = V('postfix') + V('variable') + V('number') + V('string') + V('parens') + V('unary'),
      postfix = V('new') + V('index') + V('range'), --
      new = node('new', reserved('new') * Cg(token('[') * V('expr') * token(']'))^1),
      index = fnode('index', V('variable') * Cg(token('[') * V('expr') * token(']'))^1),
      range = fnode('range',
        V('variable') *
          Cg(token('[') * (V('expr') + node('number', field('value', Cc(1)))) * token(':') *
            (V('expr') + node('number', field('value', Cc(-1)))) * token(']'))^1), --
      parens = token('(') * V('expr') * token(')'),
      unary = node('unop', field('op', op(S('-!'))) * field('expr', V('exp'))),
      exp = node('binop',
        field('left', V('primary')) * (field('op', op('^')) * field('right', V('exp')))) +
        V('primary'), -- right-associative, so cannot use fnode('binop', ...)
      mul = fnode('binop', V('exp') * Cg(op(S('*/%')) * V('exp'))^0),
      add = fnode('binop', V('mul') * Cg(op(S('+-')) * V('mul'))^0),
      concat = fnode('binop', V('add') * Cg(op('..') * V('add'))^0),
      cmp = fnode('binop', V('concat') * Cg(op(S('><') * P('=')^-1 + S('!=') * '=') * V('concat'))^0),
      land = fnode('logop', V('cmp') * Cg(op('and') * V('cmp'))^0),
      lor = fnode('logop', V('land') * Cg(op('or') * V('land'))^0), --
      expr = V('lor'),

      -- Statements.
      block = token('{') * (V('stats') + node('empty', token(';')^0)) * token('}'),
      stats = node('seq', field('left', V('stat')) * (token(';')^1 * field('right', V('stats')))) +
        V('stat') * token(';')^-1,
      stat = V('block') + V('if') + V('switch') + V('while') + V('assign') + V('print') +
        V('return'),
      ['if'] = Cf(
        node('if', reserved('if') * field('expr', V('expr')) * field('block', V('block'))) *
          node('if', reserved('elseif') * field('expr', V('expr')) * field('block', V('block')))^0 *
          node('else', reserved('else') * field('block', V('block')))^-1, fold_if),
      switch = Cf(node('switch', reserved('switch') * field('expr', V('expr'))) *
        node('if', reserved('case') * field('expr', V('expr')) * field('block', V('block')))^0 *
        node('else', reserved('else') * field('block', V('block')))^-1, fold_switch),
      ['while'] = node('while',
        reserved('while') * field('expr', V('expr')) * field('block', V('block'))),
      assign = node('assign', (field('variable', V('index') + V('variable'))) * token('=') *
        field('expr', V('expr'))), print = node('print', token('@') * field('expr', V('expr'))),
      ['return'] = node('return', reserved('return') * field('expr', V('expr'))),

      -- Utility.
      reset_pos = P(function()
        self._max_pos = 0
        return true
      end) * space, --
      save_pos = P(function(_, i)
        self._max_pos = math.max(self._max_pos, i)
        return true
      end)
    }
  end

  local ast = self._grammar:match(input)
  if not ast then
    local parsed = input:sub(1, self._max_pos - 1):gsub('\n?$', '') -- chomp
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
local NEW = 'new'
local SETINDEX = 'setindex'

-- List of opcodes for a stack machine.
local opcodes = {}

---
-- Creates a list of opcodes from the given Abstract syntax tree.
-- @param ast Abstract syntax tree to compile.
-- @see grammar.parse
function opcodes.new(ast)
  local codes = setmetatable({}, {__index = opcodes})
  codes:_add_stat(ast)
  -- Add implicit 'return 0' statement.
  codes:_add(PUSH, 0)
  codes:_add(RET)
  return codes
end

-- Adds the given opcode and optional value(s) to the list.
-- @param op Opcode to add.
-- @param ... Optional value(s) for `op`, such as a number to push or variable to store or load.
function opcodes:_add(op, ...)
  table.insert(self, (assert(op, 'attempt to add nil op')))
  for _, value in ipairs({...}) do if value then table.insert(self, value) end end
end

-- Returns a numeric ID for the given variable, creating it if possible.
-- @param id Variable to fetch an ID for.
-- @param can_create Flag that indicates whether or not an ID can be created. If `false` and
--  there is no numeric ID is available, raises an error for the undefined variable.
function opcodes:_variable_id(id, can_create)
  if not self._vars then self._vars = {} end
  if not self._vars[id] and can_create then
    table.insert(self._vars, id)
    self._vars[id] = #self._vars
  end
  return (assert(self._vars[id], 'undefined variable: ' .. id))
end

-- Adds the opcodes for the given expression node to the list.
-- @param node Abstract syntax tree node of the expression to add.
function opcodes:_add_expr(node)
  if not self._dispatch_add_expr then
    local bin_opcodes = {
      ['+'] = ADD, ['-'] = SUB, ['*'] = MUL, ['/'] = DIV, ['%'] = MOD, ['^'] = POW, ['>='] = GTE,
      ['>'] = GT, ['<='] = LTE, ['<'] = LT, ['=='] = EQ, ['!='] = NE, ['..'] = CONCAT
    }
    local un_opcodes = {['-'] = UNM, ['!'] = NOT}
    local log_opcodes = {['and'] = JMPZP, ['or'] = JMPNZP}
    self._dispatch_add_expr = setmetatable({
      number = function(self, node) self:_add(PUSH, node.value) end,
      variable = function(self, node) self:_add(LOAD, self:_variable_id(node.id)) end,
      binop = function(self, node)
        self:_add_expr(node.left)
        self:_add_expr(node.right)
        self:_add(bin_opcodes[node.op], node.op == '..' and 2 --[[CONCAT 2]] or nil)
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
            self:_add_expr(chunk) -- interpolated expression
          else
            self:_add(PUSH, chunk)
          end
        end
        if #node > 1 or type(node[1]) ~= 'string' then self:_add(CONCAT, #node) end
      end, --
      index = function(self, node)
        self:_add_expr(node.variable)
        self:_add_expr(node.expr)
        self:_add(INDEX)
      end, --
      range = function(self, node)
        self:_add_expr(node.variable)
        self:_add_expr(node.expr) -- start
        self:_add_expr(node.expr2) -- end
        self:_add(SUBSTR)
      end, --
      new = function(self, node)
        for _, size in ipairs(node) do self:_add_expr(size) end
        self:_add(NEW, #node)
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

-- Adds the opcodes for the given statement node to the list.
-- @param node Abstract syntax tree node of the statement to add.
function opcodes:_add_stat(node)
  if not self._dispatch_add_stat then
    self._dispatch_add_stat = setmetatable({
      assign = function(self, node)
        if node.variable.tag ~= 'index' then
          self:_add_expr(node.expr)
          self:_add(STORE, self:_variable_id(node.variable.id, true))
        else
          self:_add_expr(node.variable.variable)
          self:_add_expr(node.variable.expr)
          self:_add_expr(node.expr)
          self:_add(SETINDEX)
        end
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
        if node.block_else then
          local over_else = self:_jump_start(JMP)
          self:_jump_end(over_if) -- jump into else block if expr is false
          self:_add_stat(node.block_else)
          self:_jump_end(over_else) -- jump over else block if expr is true
        else
          self:_jump_end(over_if) -- jump over block if expr is false
        end
      end, --
      ['while'] = function(self, node)
        local to_expr = self:_jump_end()
        self:_add_expr(node.expr)
        local over_while = self:_jump_start(JMPZ)
        self:_add_stat(node.block)
        self:_jump_start(JMP, to_expr) -- jump back to expr in while block
        self:_jump_end(over_while) -- jump out of while block if expr is false
      end, --
      switch = function(self, node) if node.if_node then self:_add_stat(node.if_node) end end,
      empty = function() end -- no-op
    }, {__index = function(_, tag) error('unknown stat tag: ' .. tag) end})
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

---
-- Returns a new stack machine.
function machine.new() return setmetatable({}, {__index = machine}) end

local _print = print -- for @ statement so that it is never silenced

---
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
        _print(type(value) ~= 'table' and value or pt.pt(value))
      end, --
      [CONCAT] = function()
        local n = opcodes:next()
        print(CONCAT, n)
        if n > 1 then
          local chunks = {}
          for i = 1, n do table.insert(chunks, 1, stack:pop()) end
          stack:push(table.concat(chunks))
        elseif type(stack:top()) ~= 'string' then
          stack:push(tostring(stack:pop())) -- interpolated expression result
        end
      end, --
      [INDEX] = function()
        local i = self:_assert_int(stack:pop(), 'invalid index')
        print(INDEX, i)
        local value, value_type = self:_assert_indexible(stack:pop())
        assert(i <= #value, 'index out of range')
        stack:push(value_type == 'string' and string.sub(value, i, i) or value[i])
      end, --
      [SUBSTR] = function()
        local e = self:_assert_int(stack:pop(), 'invalid range end')
        local s = self:_assert_int(stack:pop(), 'invalid range start')
        print(SUBSTR, s, e)
        local value, value_type = self:_assert_indexible(stack:pop())
        stack:push(string.sub(value, s, e))
      end, --
      [NEW] = function()
        local n = opcodes:next()
        print(NEW, n)
        local dims = {}
        for i = 1, n do table.insert(dims, 1, self:_assert_int(stack:pop(), 'invalid size')) end
        local function new_array(size)
          return setmetatable({n = size}, {__len = function(t) return t.n end})
        end
        local function add_dimension(t, n)
          if n > #dims then return end
          for i = 1, #t do
            t[i] = new_array(dims[n])
            add_dimension(t[i], n + 1)
          end
        end
        local t = new_array(dims[1])
        if #dims > 1 then add_dimension(t, 2) end
        stack:push(t)
      end, --
      [SETINDEX] = function()
        local value = stack:pop()
        local i = self:_assert_int(stack:pop(), 'invalid index')
        local array = stack:pop()
        assert(type(array) == 'table', 'cannot set index for non-array value')
        print(SETINDEX, '<array>', i, value)
        array[i] = value
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

    for _, opcode in ipairs{JMP, JMPZ, JMPZP, JMPNZP} do
      self._dispatch[opcode] = function()
        local rel = opcodes:next()
        print(opcode, rel)
        local zero = stack:top() == 0
        local jump = opcode == JMP or ((opcode == JMPZ or opcode == JMPZP) and zero) or
          (opcode == JMPNZP and not zero)
        local pop = opcode == JMPZ or (opcode == JMPZP and not zero) or (opcode == JMPNZP and zero)
        if jump then opcodes:jump(rel) end
        if pop then
          print('pop') -- not an opcode, but verify pop operation
          stack:pop()
        end
      end
    end
  end

  -- Execute instructions.
  local dispatch = self._dispatch
  while true do if dispatch[opcodes:next()]() then break end end

  return stack:pop()
end

-- Asserts the given value is an integer type and returns that value.
function machine:_assert_int(value, message)
  return (assert(math.tointeger(value), message))
end

-- Asserts the given value is of an indexible type and returns that value and its type.
function machine:_assert_indexible(value)
  local value_type = type(value)
  if value_type ~= 'string' and value_type ~= 'table' then
    error(string.format('cannot index %s value', value_type))
  end
  return value, value_type
end

-- ===============================================================================================--
-- Module.

---
-- Interpreter module.
local M = {grammar = grammar.new()}

---
-- Runs the given input code and returns its result.
-- @param input Input code to run.
-- @param verbose Optional flag that indicates whether or not print debug info when running. Debug
--   info includes the Abstract Syntax Tree and opcodes.
function M.run(input, verbose)
  local _print = print
  print = function(...) if verbose then _print(...) end end

  print(input)
  local ok, result = xpcall(function()
    local ast = M.grammar:parse(input)
    print(pt.pt(ast))
    return machine.new():run(opcodes.new(ast))
  end, debug.traceback)

  print = _print -- restore
  return assert(ok and result, result)
end

return M
