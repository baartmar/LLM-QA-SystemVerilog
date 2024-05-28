from model import LLM
from dataset import SystemVerilogDataset, TEST_DIR
import torch

device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
data = SystemVerilogDataset(TEST_DIR)
models = ['google/flan-t5-xxl']
for model in models:
    llm = LLM(model, device)
    llm.evaluate_model(data)