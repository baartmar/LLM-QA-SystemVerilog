import os
import json
import copy
from utils import *

ENTRY = {
    'passage': '',
    'questions': [],
    'type': 0,
    'comments': 0,
    'source': '',
    'tags': []
}

QUESTION = {
    'question': 'question',
    'answers': [
        '', '', ''
    ],
    'type': 0,
    'difficulty': 0,
    'sv_standard_sections': [],
    'tags': []
}

ADVERSARIAL_QUESTION = {
    'question': 'question',
    'answers': [],
    'type': 0,
    'difficulty': 0,
    'sv_standard_sections': [],
    'tags': []
}

if not os.path.exists(DATASET_DIR):
    os.makedirs(DATASET_DIR)

if not os.path.exists(TRAIN_DIR):
    os.makedirs(TRAIN_DIR)

if not os.path.exists(VAL_DIR):
    os.makedirs(VAL_DIR)

if not os.path.exists(TEST_DIR):
    os.makedirs(TEST_DIR)

entries = os.listdir(TEST_DIR)
i = len(entries)
entry_dir = os.path.join(TEST_DIR, str(i))
if not os.path.exists(entry_dir):
    os.makedirs(entry_dir)

q1, q2, q3 = copy.deepcopy(QUESTION), copy.deepcopy(QUESTION), copy.deepcopy(QUESTION)
q2['difficulty'], q3['difficulty'] = 1, 2
entry = ENTRY
entry['questions'] = [q1, q2, q3, ADVERSARIAL_QUESTION]
with open(os.path.join(entry_dir, 'questions.json'), 'w') as f:
    json.dump(entry, f)
