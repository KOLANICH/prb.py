#!/usr/bin/env python3
import sys
from pathlib import Path
import unittest
from zlib import crc32


thisDir = Path(__file__).parent
sys.path.insert(0, str(thisDir.parent))
testFile = thisDir / "mafia_2.prb"

from collections import OrderedDict

dict = OrderedDict

import prb
from prb import PRB


class Tests(unittest.TestCase):

	def testSimple(self):
		problem = PRB(testFile)
		problem.description.text.find("psycho")
		self.assertEqual(crc32(problem.description.text.encode("utf-8")), 2500270635)
		f = problem.orig.mappingFacts[0]
		self.assertEqual(f.paragraphNo, 1)

		self.assertEqual(f.entities[0].dimension.name, 'Nickname')
		self.assertEqual(f.entities[0].id, 'Paul')
		self.assertEqual(f.entities[1].dimension.name, 'Role')
		self.assertEqual(f.entities[1].id, 'doc')


if __name__ == "__main__":
	unittest.main()
