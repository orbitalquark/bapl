local interpreter = require('interpreter')

-- Tests the given statement returns the given expected value.
-- @param stat Statement or list of statements to run.
-- @param expected Value expected to be returned by `stat`.
-- @param verbose Optional flag that indicates whether or not to print debug info.
local function test_stat(stat, expected, verbose)
  local actual = interpreter.run(stat, verbose)
  assert(expected, 'expected result not given')
  assert(actual == expected, string.format("%s == %q (expected %q)", stat, actual, expected))
end

-- Tests the given expression returns an optional expected value.
-- @param expr Expression to evaluate.
-- @param expected Optional value expected to be returned by `expr`. If omitted, `expr` is
--   executed using Lua and its returned value is used for the test.
-- @param verbose Optional flag that indicates whether or not to print debug info.
function test_expr(expr, expected, verbose)
  test_stat('return ' .. expr, expected or assert(load('return ' .. expr))(), verbose)
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

-- Test unary not.
test_expr('!1', 0)
test_expr('!2', 0)
test_expr('!!1', 1)
test_expr('!0-!0', 0)
test_expr('!(1+2<3*4)', 0)
test_expr('!1!=!1', 0)

-- Test simple assignments and return statements.
test_stat('x=1;return x', 1)
test_stat('x=1;return(x)', 1)
test_stat('_abc123=1;;return _abc123', 1)
-- test_stat('x=y=1;return x', 1)

-- Test blocks.
test_stat(' { x = 1 ; } ; { y = 2 } ; { return x + y } ', 3)
test_stat('x=1;{y=2;return x+y}', 3)
test_stat([[
x = 1;
y = 2;
return x + y]], 3)
test_stat('{};;{;;};{ { } };', 0) -- empty blocks and statements

-- Test print statement.
test_stat('@(2*2)', 0)
test_stat('x=-(2*2);@x', 0)

-- Test use of variables before assignment at compile time.
local ok, err = pcall(test_stat, 'return 1+y')
assert(not ok and err:find('undefined variable: y'), 'expected "undefined variable: y"')

-- Test syntax error.
ok, err = pcall(test_stat, 'oops!')
assert(not ok and err:find('syntax error at line 1, col 5'))
ok, err = pcall(test_stat, [[
x = 1;
oops!]])
assert(not ok and err:find('syntax error at line 2, col 5'))
ok, err = pcall(test_stat, [[
x = 1;
y = 2
return x + y
]])
assert(not ok and err:find('syntax error at line 2, col 6'))

-- Test comments.
test_stat([[
#{comment
comment#}
x = 1; # comment
# comment
y = 2;
return x + y]], 3)

-- Test reserved words.
ok, err = pcall(test_stat, 'x=1;returnx')
assert(not ok and err:find('syntax error'))
ok, err = pcall(test_stat, 'return1')
assert(not ok and err:find('syntax error'))
test_stat('returnx=1;return returnx', 1)
ok, err = pcall(test_stat, 'return=1;return return')
assert(not ok and err:find('syntax error'))

-- Test if conditionals.
test_stat('if 1 { return 1 }', 1)
test_stat('if 0 { return 1 }', 0)
test_stat('if 1 { return 1 } else { return 2 }', 1)
test_stat('if 0 { return 1 } else { return 2 }', 2)
test_stat([[
a = 2;
if a == 0 {
  return 1
} elseif a == 1 {
  return 2
} else {
  return 3
}]], 3)
test_stat(
  'if 0 { if 1 { return 1 } else { return 2 } } else { if 1 { return 3 } else { return 4} }', 3)
test_stat('if 1 {} else {return 1}', 0)

-- Test while.
test_stat('x = 0; while x < 10 { x = x + 1}; return x', 10)
test_stat([[
i = 6;
factorial = 1;
while i {
  factorial = factorial * i;
  i = i - 1
};
return factorial]], 720)

-- Test logical operators.
test_expr('4 and 5')
test_expr('0 and 3', 0)
test_expr('0 or 10', 10)
test_expr('2 or 3')
test_expr('1 and 2 or 3', 2)
test_expr('0 and 1 or 2', 2)
test_stat('x = 1 and 0; return x', 0)
test_stat('x = 0 and 1; return x', 0)
test_stat('x = 0 or 1; return x', 1)
test_stat('x = 1 or 0; return x', 1)
test_stat('x=(1==1)and(0==0)or!(0==0);return x', 1)
test_stat('x=(1==1)and!(0==0)or!(0==0);return x', 0)

-- Test switch.
test_stat([[
switch 1 + 2
case 1 { return 1 }
case 2 { return 2 }
else { return 3 }]], 3)
test_stat([[
x = 2;
switch x
case 1 { return 1 }
case 2 { return 2 }
else { return 3 }]], 2)
test_stat('switch 0 else { return 1 }', 1)
test_stat('switch 1; return 2', 2)

-- Test strings.
test_expr([["foo"]], 'foo')
test_expr([["\"foo\""]], '"foo"')
test_expr([["foo\"bar"]], 'foo"bar')
test_expr([["foo\\bar"]], 'foo\\bar')
test_expr([["foo\tbar"]], 'foo\tbar')
test_expr([["foo\x20bar"]], 'foo bar')
test_expr([["foo
bar"]], 'foo\nbar')
test_expr([["1 + 2 = `1+2`"]], '1 + 2 = 3')
test_expr([["`1 + 2` == `1+2`"]], '3 == 3')
test_expr([["`1+2`"]], '3')
test_expr([["foo`"bar"`baz"]], 'foobarbaz')
ok, err = pcall(test_stat, [[x="foo\ybar"]])
assert(not ok and err:find('syntax error'))

-- Test concatenation.
test_expr([["foo" .. "bar"]], 'foobar')
test_expr([["foo" .. 1]], 'foo1')
test_expr([[1+2 .. "foo"]], '3foo')

-- Test indexing.
test_stat('x="foo";return x[1]', 'f')
test_stat('x="foobar";return x[-1]', 'r')
test_stat('x="foobar";return x[2*2]', 'b')
test_stat('x="foo";return x[1:2]', 'fo')
test_stat('x="foo";return x[1:1+1]', 'fo')
test_stat('x="foo";return x[:]', 'foo')
test_stat('x="foo";return x[:-1]', 'foo')
test_stat('x="foo";return x[2:]', 'oo')
test_stat('x="foo";return x[2*(1==1):]', 'oo')
test_stat('x="foo";return x[:2]', 'fo')

ok, err = pcall(test_stat, 'x="foo";return x["foo"]')
assert(not ok and err:find('invalid index'))
ok, err = pcall(test_stat, 'x="foo";return x["foo":]')
assert(not ok and err:find('invalid range start'))
ok, err = pcall(test_stat, 'x="foo";return x[:"foo"]')
assert(not ok and err:find('invalid range end'))
ok, err = pcall(test_stat, 'x=1;return x[2]')
assert(not ok and err:find('cannot index number value'))
ok, err = pcall(test_stat, 'x=1;return x[2:3]')
assert(not ok and err:find('cannot index number value'))

print('Passed')
