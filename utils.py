import os

SV_STANDARD_SECTIONS_MAP = {
    3: 'Design and Verification Bulding Blocks',
    4: 'Scheduling Semantics',
    5: 'Lexical Conventions',
    6: 'Data Types',
    7: 'Aggregate Data Types',
    8: 'Classes',
    9: 'Processes',
    10: 'Assignment Statements',
    11: 'Operators and Expressions',
    12: 'Procedural Programming Statements',
    13: 'Tasks and Functions (Subroutines)',
    14: 'Clocking Blocks',
    15: 'Interprocess Synchronization and Communication',
    16: 'Assertions',
    17: 'Checkers',
    18: 'Constrained Random Value Generation',
    19: 'Functional Coverage',
    20: 'Utility System Tasks and System Functions',
    21: 'Input/Output System Tasks and System Functions',
    22: 'Compiler Directives'
}

PASSAGE_TYPES = {
    0: 'Design',
    1: 'Verification',
    2: 'Design & Verification'
}

QUESTION_DIFFICULTY = {
    0: 'Easy',
    1: 'Medium',
    2: 'Hard'
}

COMMENTS = {
    0: 'None',
    1: 'Some',
    2: 'Lots'
}

QUESTION_TYPE = {
    0: 'Design',
    1: 'Verification',
    2: 'Design & Verification',
    3: 'Syntax',
    4: 'Other'
}

DATASET_DIR = 'data'
TRAIN_DIR = os.path.join(DATASET_DIR, 'train')
VAL_DIR = os.path.join(DATASET_DIR, 'val')
TEST_DIR = os.path.join(DATASET_DIR, 'test')
FIGURES_DIR = 'figures/'