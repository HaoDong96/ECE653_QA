import unittest
import wlang.ast as ast
import wlang.stats_visitor as stats_visitor

class TestStatsVisitor (unittest.TestCase):
    def test_one (self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string (prg1)

        sv = stats_visitor.StatsVisitor ()
        sv.visit (ast1)
        # UNCOMMENT to run the test
        self.assertEquals (sv.get_num_stmts (), 2)
        self.assertEquals (sv.get_num_vars (), 1)

    def test_stats_visitor(self):
        prg1 = """{a := 1;
              b := -1;
              c := a + b; d := b - a;
              e := a * b; f := a / b};
              if a > 1 and a >= b then b := 3; 
              if a <= 1 or b < 3 then a := 1; 
              if false and not a = 1 then a := 1 else print_state; 
              skip;
              print_state;
              while (a < 3) and true do {a := a + 1};
              assume b = -1;
              havoc c,d;
              assert a = 3"""
        ast1 = ast.parse_string (prg1)
        sv = stats_visitor.StatsVisitor ()
        sv.visit (ast1)
        self.assertEquals (sv.get_num_stmts (), 20)
        self.assertEquals (sv.get_num_vars (), 6)