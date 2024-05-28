import os
import json
from typing import List
import torch
from torch.utils.data import Dataset
from utils import *
import matplotlib.pyplot as plt

class Question():
    def __init__(self, passage, question, answers, question_type, difficulty, sections, tags, id):
        self.passage = passage
        self.question = question
        self.id = id
        self.answers = answers
        self.question_type = QUESTION_TYPE[question_type]
        self.difficulty = QUESTION_DIFFICULTY[difficulty]
        self.sections = sections
        self.tags = tags
    
    def to_prompt(self):
        return f"""Retrieve the span of text from the code which answers the question. If the question cannot be answered, output “No Answer”. Output only the retrieved text from the code, do not give any explanation.\nCode: {self.passage}\nQuestion: {self.question}\nAnswer:"""
    
    def to_squad_format(self):
        return {'id': self.id, 'prediction_text': '', 'no_answer_probability': 0.}, {'answers': [{'text': [answer]} for answer in self.answers], 'id': self.id, 'no_answer_threshold': 1. if not self.answers else 0.}

class SystemVerilogDataset(Dataset):
    def __init__(self, root_dir) -> None:
        self.root_dir = root_dir
        self.questions: List[Question] = []
        self.tags = {}
        self.sv_sections = {}
        self.passage_types = {}
        self.question_types = {}
        self.difficulties = {}
        self.no_answers = 0
        self.comments = {}

        for entry in os.listdir(root_dir):
            fp = os.path.join(root_dir, entry)
            with open(os.path.join(fp, 'questions.json'), 'r', errors='ignore') as f:
                questions = json.load(f)
            with open(os.path.join(fp, questions['passage']), 'r', errors='ignore') as f:
                passage = f.read()
            for index, question in enumerate(questions['questions']):
                q = Question(passage, question['question'], question['answers'], question['type'], question['difficulty'], question['sv_standard_sections'], question['tags'], index)
                for section in q.sections:
                    if section not in self.sv_sections:
                        self.sv_sections[section] = 1
                    else:
                        self.sv_sections[section] += 1
                
                if q.question_type not in self.question_types:
                    self.question_types[q.question_type] = 1
                else:
                    self.question_types[q.question_type] += 1
                
                if q.difficulty not in self.difficulties:
                    self.difficulties[q.difficulty] = 1
                else:
                    self.difficulties[q.difficulty] += 1

                if not q.answers:
                    self.no_answers += 1

                self.questions.append(q)
            
            
            for tag in questions['tags']:
                if tag not in self.tags:
                    self.tags[tag] = 1
                else:
                    self.tags[tag] += 1

            psg_type = PASSAGE_TYPES[questions['type']]
            if psg_type not in self.passage_types:
                self.passage_types[psg_type] = 1
            else:
                self.passage_types[psg_type] += 1

            comment_level = COMMENTS[questions['comments']]
            if comment_level not in self.comments:
                self.comments[comment_level] = 1
            else:
                self.comments[comment_level] += 1
    
    def __len__(self):
        return len(self.questions)
    
    def __getitem__(self, index):
        if torch.is_tensor(index):
            index = index.tolist()
        
        return self.questions[index]
    
    def plot_summary(self):
        if not os.path.exists(FIGURES_DIR):
            os.makedirs(FIGURES_DIR)
        
        
        plt.pie(self.tags.values(), labels=self.tags.keys(), autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("Tags")
        plt.savefig(os.path.join(FIGURES_DIR, 'tags.png'))
        plt.close()
        plt.pie(self.comments.values(), labels=self.comments.keys(), autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("Level of Commenting in Dataset Code Snippets")
        plt.savefig(os.path.join(FIGURES_DIR, 'comments.png'))
        plt.close()
        plt.pie(self.passage_types.values(), labels=self.passage_types.keys(), autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("Types of Code Snippets (Passages) in Dataset")
        plt.savefig(os.path.join(FIGURES_DIR, 'passagetypes.png'))
        plt.close()
        plt.pie(self.question_types.values(), labels=self.question_types.keys(), autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("Types of Questions in Dataset")
        plt.savefig(os.path.join(FIGURES_DIR, 'questiontypes.png'))
        plt.close()
        plt.pie(self.sv_sections.values(), labels=self.sv_sections.keys(), autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("SV Standard Sections in Dataset")
        plt.savefig(os.path.join(FIGURES_DIR, 'svsections.png'))
        plt.close()
        plt.pie(self.difficulties.values(), labels=self.difficulties.keys(), autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("Question Difficulties")
        plt.savefig(os.path.join(FIGURES_DIR, 'difficulties.png'))
        plt.close()
        plt.pie([len(self.questions) - self.no_answers, self.no_answers], labels=['Answerable', 'No Correct Answer'], autopct=lambda p: '{:.0f}%'.format(p))
        plt.title("Adversarial Questions")
        plt.savefig(os.path.join(FIGURES_DIR, 'adversarial.png'))
        plt.close()
    

#data = SystemVerilogDataset(TEST_DIR)
#data.plot_summary()
            
        