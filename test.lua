local interpreter = require('interpreter')

-- Tests the given statement returns the given expected value.
-- @param stat Statement or list of statements to run.
-- @param expected Value expected to be returned by `stat`.
local function test_stat(stat, expected)
  local actual = interpreter.run(stat)
  assert(actual == expected, string.format("'%s' ~= %f (expected %f)", expr, actual, expected))
end

-- Tests the given expression returns an optional expected value.
-- @param expr Expression to evaluate.
-- @param expected Optional value expected to be returned by `expr`. If omitted, `expr` is
--   executed using Lua and its returned value is used for the test.
function test_expr(expr, expected)
  test_stat('return ' .. expr, expected or assert(load('return ' .. expr))())
end

-- Test integers, floats, and hex numbers.
test_expr('1')
test_expr('1.0e1')
test_expr('1.0e+1')
test_expr('10E-1')
test_expr('0xa')
test_expr('0XFF')

-- Test simple expressions and order-of-operations.
test_expr('1+2')
test_expr('2 - 1')
test_expr('10/2')
test_expr('1+2*3-4')
test_expr('3%2')
test_expr('2^3^4')
test_expr('1000/10/10')

-- Test parenthesized expressions.
test_expr('(1+2)*(3+4)')
test_expr(' ( 1 + 2 ) * ( 3 / 4 ) ')

-- Test unary minus.
test_expr('-1')
test_expr('-10.50')
test_expr('- -1')
test_expr('10*-1')
test_expr('-(1+2)')
test_expr('-1+2')
test_expr('-(1-2)*-3*(4/5)')
test_expr('-2^2')
test_expr('2^-2')

-- Test comparisons.
test_expr('1==1', 1)
test_expr('1!=1', 0)
test_expr('1+2<3*4', 1)
test_expr('0/1<=-(2-2)/3', 1)
test_expr('2^2>2^2', 0)
test_expr('1*2>=8/4', 1)
test_expr('1!=-1==1', 1)

-- Test simple assignments and return statements.
test_stat('x=1;return x', 1)
test_stat('_abc123=1;;return _abc123', 1)

-- Test blocks.
test_stat(' { x = 1 ; } ; { y = 2 } ; ; { return x + y } ', 3)
test_stat('x=1;{y=2;;return x+y}', 3)
test_stat([[
x = 1;
y = 2;
return x + y]], 3)

-- Test print statement.
test_stat('@(2*2)', 0)
test_stat('x=-(2*2);@x', 0)

-- Test use of variables before assignment at compile time.
local ok, err = pcall(test_stat, 'return 1+y')
assert(not ok and err:find('undefined variable: y'), 'expected "undefined variable: y"')

print('Passed')
