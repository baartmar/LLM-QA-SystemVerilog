from dataset import SystemVerilogDataset, Question
from transformers import T5Tokenizer, T5ForConditionalGeneration, AutoTokenizer, AutoConfig, AutoModelForCausalLM, pipeline
#from openai import OpenAI
#import openai
#import tiktoken
from huggingface_hub import login
import torch
from evaluate import load
from tqdm import tqdm
import json
import os

squad_metric = load("squad_v2")
ACCESS_TOKEN=""
login(ACCESS_TOKEN)
class LLM():
    def __init__(self, model_name, device, temperature=0, tokenizer_name=None) -> None:
        self.device = device
        self.temperature = temperature
        self.model_name = model_name
        self.config = AutoConfig.from_pretrained(model_name)
        if self.config.model_type == 't5':
            self.tokenizer = T5Tokenizer.from_pretrained(tokenizer_name if tokenizer_name is not None else model_name)

            self.llm = T5ForConditionalGeneration.from_pretrained(model_name, device_map='auto', torch_dtype=torch.float16)
        else:
            self.pipe = pipeline(task='text-generation', model=model_name, torch_dtype=torch.bfloat16, device_map="auto", max_new_tokens=100, return_full_text=False)
        """
        elif any(chat_keyword in self.model_name for chat_keyword in ["it", "chat", "Instruct", "vicuna", 'llama']):
            self.tokenizer = AutoTokenizer.from_pretrained(tokenizer_name if tokenizer_name is not None else model_name)
            self.tokenizer.use_default_system_prompt = False
            self.llm = AutoModelForCausalLM.from_pretrained(model_name, device_map='auto', torch_dtype=torch.float16 if device == 'cuda' else torch.float32).eval()
        """

    def answer_question(self, question:Question):
        if self.config.model_type == 't5':
            input_ids = self.tokenizer([question.to_prompt(chat=False)], return_tensors="pt").input_ids.to(self.llm.device)
            output_ids = self.llm.generate(input_ids, max_new_tokens=50)
            output = self.tokenizer.batch_decode(output_ids, skip_special_tokens=True)[0]
        else:
            terminators = [
                self.pipe.tokenizer.eos_token_id,
                self.pipe.tokenizer.convert_tokens_to_ids("<|eot_id|>")
            ]

            output = self.pipe(question.to_prompt(chat=not 'vicuna' in self.model_name), eos_token_id=terminators)[0]['generated_text']
        prediction, reference = question.to_squad_format()
        print(output)
        prediction['prediction_text'] = output
        torch.cuda.empty_cache()
        if 'no answer' in output.lower():
            prediction['prediction_text'] = []
            prediction['no_answer_probability'] = 1.
            prediction['answer_start'] = []
        return prediction, reference

    def evaluate_model(self, data:SystemVerilogDataset, output_dir):
        predictions, references = [], []
        for idx, question in enumerate(tqdm(data.questions)):
            prediction, reference = self.answer_question(question)
            predictions.append(prediction)
            references.append(reference)

        results = squad_metric.compute(predictions=predictions, references=references)
        with open(os.path.join(output_dir, f'{self.model_name.replace("/", "-")}.json'), 'w') as f:
            json.dump({'predictions': predictions, 'references': references}, f)
        results['model'] = self.model_name
        return results
