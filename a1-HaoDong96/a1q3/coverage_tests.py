import unittest
from a1q3 import M
from StringIO import StringIO
import sys



class CoverageTests (unittest.TestCase):

    def change_stdout(self):
        """save original stdout to old_output for saving it back
        new a stringIO
        point stdout(what print() print) to new_output """
        old_output = sys.stdout 
        self.new_output = StringIO() 
        sys.stdout = self.new_output 


    def test_1 (self):
        """TR_{NC} = {[3, 8, 9, 12, 13, 14, 17, 18, 21, 23, 24, 25, 27]}
        Satisfy node 8 by assigning 0 to i, 
        and then change the length of arg to run all possible cases
        then use assertEqual to check the print result every time"""
        o = M ()
        self.change_stdout()

        o.m('', 0)  # 3,8,9,12,23,25,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'zero') # get the last output and check

        o.m('t', 0) # 3,8,9,13,14,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'a')

        o.m('te', 0) # 3,8,9,13,17,18,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')

        o.m('tes', 0) # 3,8,9,13,17,21,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')
        pass


    def test_2 (self):
        """TR_{EC} = { [3,8], [3,9], [8,9], [9,12], [9,13], [13,14], 
        [13,17], [17,18], [17,21], [12,23], [14,23], [18,23], [21,23], 
        [23,24], [23,25], [24,27], [25,27] }
        test_1 does not cover the path(3,9), assign 1 to i to satisfy this"""
        o = M ()
        self.change_stdout()

        o.m('', 1)  # 3,9,12,23,25,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'zero')

        o.m('t', 0) # 3,8,9,13,14,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'a')

        o.m('te', 0) # 3,8,9,13,17,18,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')
        
        o.m('tes', 0) # 3,8,9,13,17,21,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')
        pass


    def test_3 (self):
        """TR_{EPC} = {[3,8,9], [3,9,12], [3,9,13], [8,9,12], [8,9,13], 
        [9,12,23], [9,13,14], [9,13,17], [12,23,25], [13,14,23], [13,17,18],
         [13,17,21], [14,23,24], [17,18,23], [17,21,23], [18,23,24], 
         [21,23,24], [23,24,27], [23,25,27]}
         test_2 does not cover [8,9,12], make node 8 and 12 happens at the same time
         test_2 does not cover [3,9,13], make node 8 and 12 disappear"""
        o = M ()
        self.change_stdout()

        o.m('', 1)  # 3,9,12,23,25,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'zero')

        o.m('t', 1)  # 3,9,13,14,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'a')

        o.m('', 0)  # 3,8,9,12,23,25,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'zero')

        o.m('t', 0) # 3,8,9,13,14,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'a')

        o.m('te', 0) # 3,8,9,13,17,18,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')

        o.m('tes', 0) # 3,8,9,13,17,21,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')
        pass


    def test_4 (self):
        """TR_{PPC} = {[3,8,9,12,23,25,27],[3,9,12,23,25,27], [3,8,9,13,14,23,24,27],
         [3,9,13,14,23,24,27], [3,8,9,13,17,18,23,24,27],[3,9,13,17,18,23,24,27], 
         [3,8,9,13,17,21,23,24,27],[3,9,13,17,21,23,24,27] }
         all paths need to be covered"""
        o = M ()
        self.change_stdout()

        o.m('', 0)  # 3,8,9,12,23,25,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'zero')

        o.m('', 1)  # 3,9,12,23,25,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'zero')

        o.m('t', 0) # 3,8,9,13,14,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'a')

        o.m('t', 1) # 3,9,13,14,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'a')

        o.m('te', 0) # 3,8,9,13,17,18,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')

        o.m('te', 1) # 3,9,13,17,18,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')

        o.m('tes', 0) # 3,8,9,13,17,21,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')

        o.m('tes', 1) # 3,9,13,17,21,23,24,27
        self.assertEqual(self.new_output.getvalue().split('\n')[-2],'b')
        pass
    
