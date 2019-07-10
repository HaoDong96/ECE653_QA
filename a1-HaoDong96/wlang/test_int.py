# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import unittest
import wlang.ast as ast
import wlang.int
import wlang.parser as parser
import sys
import os


class MyAstVisitor(ast.AstVisitor):
    # some of methods of AstVisitor are override by Interpreter,
    # this variable is used to test them

    def __init__(self):
        super(MyAstVisitor, self).__init__()

    def visit_StmtList(self, node, *args, **kwargs):
        for s in node.stmts:
            self.visit(s)

    def visit_Stmt(self, node, *args, **kwargs):
        pass

    def visit_Exp(self, node, *args, **kwargs):
        pass


class TestInt(unittest.TestCase):

    def test_one(self):
        prg1 = "x := 10; print_state"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = wlang.int.Interpreter()
        st = wlang.int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn('x', st.env)
        # x is 10
        self.assertEquals(st.env['x'], 10)
        # no other variables in the state
        self.assertEquals(len(st.env), 1)

    ################################################################################
    # test ast.py and parse.py
    ################################################################################
    def test_ast_parse(self):
        my_astvisitor = MyAstVisitor()
        # test suite
        prg = """{a := 1;
              b := -1;
              c := a + b; d := b - a;
              e := a * b; f := a / b};
              if a > 1 and a >= b then b := 3; 
              if a <= 1 or b < 3 then a := 1; 
              if false and not a = 1 then a := 1 else print_state; 
              skip;
              print_state;
              while (a < 3) or (b = 1) and true do {a := a + 1};
              assume b = -1;
              havoc c,d;
              assert a = 3;
              assert a = 2"""
        # test parse
        ast1 = ast.parse_string(prg)
        self.assertIsNotNone(ast1)
        # test _repr_ ,_str_  and PrintVisitor through _str_
        repr(ast1)
        # test _eq_ func of every class
        self.t_ast_eq_(ast1)
        # test AstVisitor in ast.py
        my_astvisitor.visit(ast1)
        return ast1

    def t_ast_eq_(self, ast1):
        # test _eq_ func of every class
        self.assertTrue(ast1 == ast1)  # StmtList
        self.assertTrue(ast1.stmts[1] == ast1.stmts[1])  # IfStmt
        self.assertTrue(ast1.stmts[4] == ast1.stmts[4])  # SkipStmt
        self.assertTrue(ast1.stmts[5] == ast1.stmts[5])  # PrintStmt
        self.assertTrue(ast1.stmts[6] == ast1.stmts[6])  # WhileStmt
        self.assertTrue(ast1.stmts[7] == ast1.stmts[7])  # AssumeStmt
        self.assertTrue(ast1.stmts[8] == ast1.stmts[8])  # HavocStmt
        ast1.stmts[9] == ast1.stmts[9]  # AssertStmt

    def test_ast_Exp_binary(self):
        exp = ast.Exp('+',['a','b'])
        exp.is_binary()
    
    def test_ast_PrintVisitor_none(self):
        printVisitor = ast.PrintVisitor(None)
        printVisitor.visit_StmtList(ast.StmtList(None))
     
    def test_ast_Const(self):
        const = ast.Const(1)
        repr(const)
        str(const)
        hash(const)

    def test_ast_IntVar(self):
        my_astvisitor = MyAstVisitor()
        intvar = ast.IntVar('a := 1')
        my_astvisitor.visit(intvar)
        repr(intvar)
        str(intvar)
        hash(intvar)

    def test_ast_file(self):
        self.assertIsNotNone(ast.parse_file('wlang/test1.prg'))

    ################################################################################
    # test int.py
    ################################################################################
    def test_Int(self):
        ast1 = self.test_ast_parse()
        # test interpreter init
        interp = wlang.int.Interpreter()
        st = wlang.int.State()

        # test _repr_ of State
        # there is a bug here that repr will return non-string 
        try:
            repr(st)
        except TypeError:
            pass

        # test interpreter
        try:
            st = interp.run(ast1, st)
        except AssertionError:
            pass
        self.assertIsNotNone(st)

        # a,b,c,d,e,f are defined
        self.assertIn('a', st.env)
        self.assertIn('b', st.env)
        self.assertIn('c', st.env)
        self.assertIn('d', st.env)
        self.assertIn('e', st.env)
        self.assertIn('f', st.env)
        # test values of variables
        self.assertEqual(st.env['a'], 3)
        self.assertEqual(st.env['b'], -1)
        self.assertEqual(st.env['c'], 0)
        self.assertEqual(st.env['d'], 0)
        self.assertEqual(st.env['e'], -1)
        self.assertEqual(st.env['f'], -1)
        # test the length of state
        self.assertEquals(len(st.env), 6)

    ################################################################################
    # test parse.py
    ################################################################################
    def test_parse_WhileLangSemantics(self):
        prg = "a := 1"
        ast1 = ast.parse_string(prg)
        while_lang = parser.WhileLangSemantics()
        while_lang_methods = [method for method in dir(while_lang)
                              if callable(getattr(while_lang, method))
                              if not method.startswith('_')]  # 'private' methods start from _
        for method in while_lang_methods:
            getattr(while_lang, method)(ast1)  # call
        

    ################################################################################
    # Explanation for each line that was not covered:
    ################################################################################
    #
    # Int.py:68   For RelExp, there is no possible to turn to assert False
    #
    # parse.py:114    For _stmt_, there is no possible to turn to self._error
    #
    # parse.py:264    For _bfactor_, there is no possible to turn to self._error
    #
    # parse.py:448    It's difficult to create a newline
