from model import LLM
from dataset import SystemVerilogDataset, TEST_DIR
import torch
import argparse
import os
import csv
import logging
import time

#torch.seed(919)

parser = argparse.ArgumentParser()
parser.add_argument("--models", nargs='*')
parser.add_argument("--output-dir")
args = parser.parse_args()
models = args.models
output_dir = args.output_dir
if not os.path.exists(output_dir):
    os.makedirs(output_dir)

logger = logging.getLogger(__name__)
logging.basicConfig(filename=os.path.join(output_dir, 'evaluation.log'), encoding='utf-8', level=logging.DEBUG, format='%(asctime)s %(message)s', datefmt='%m/%d/%Y %I:%M:%S %p')

device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
data = SystemVerilogDataset(TEST_DIR)
logger.info('Dataset fetched.')
fields = ['model', 'duration', 'exact', 'f1', 'total', 'HasAns_exact', 'HasAns_f1', 'HasAns_total', 'NoAns_exact', 'NoAns_f1', 'NoAns_total', 'best_exact', 'best_exact_thresh', 'best_f1', 'best_f1_thresh']
rows = []
logger.info(f'Starting evaluation for {len(models)} models.')
for model in models:
    start_time = time.time()
    logger.info(f"Currently evaluating: {model}")
    llm = LLM(model, device)
    row = llm.evaluate_model(data, output_dir)
    duration = time.time() - start_time
    row['duration'] = duration
    rows.append(row)
logger.info('Evaluation complete.')

with open(os.path.join(output_dir, 'summary.csv'), 'w') as csvfile:
    writer = csv.DictWriter(csvfile, fieldnames=fields)
    writer.writeheader()
    writer.writerows(rows)
