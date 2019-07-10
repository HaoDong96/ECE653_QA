import unittest
import wlang.ast as ast
import wlang.undef_visitor as undef_visitor


class TestStatsVisitor(unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; y := x + z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(set([ast.IntVar('z')]), uv.get_undefs())

    def test_undef_visitor(self):
        prg1 = """
                a := 1;
                b := -1;
               if a > 1 and a >= b then b := 3; 
               if a <= 1 or b < 3 then a := c; 
               if false and not a = 1 then a := 1 else e := 2; 
               skip;
               print_state;
               while (a < 3) and true do {a := a + 1};
               assume b = -1;
               havoc c,d;
               assert a = 3;
               d := a + e
            """
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('c'), ast.IntVar('e')]), uv.get_undefs())
