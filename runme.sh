source "/nfs/stak/users/baartmar/hpc-share/LLM-QA-SystemVerilog/.venv/bin/activate"
module load cuda/12.1 openssl
export HUGGINGFACE_HUB_CACHE="/nfs/stak/users/baartmar/hpc-share/LLM-QA-SystemVerilog/.cache"
export HF_DATASETS_CACHE="/nfs/stak/users/baartmar/hpc-share/LLM-QA-SystemVerilog/.datasets"
#huggingface-cli login --token $HUGGINGFACE_TOKEN --add-to-git-credential
#python3 -W ignore run.py --models google/flan-t5-xl google/flan-t5-xxl google/flan-ul2 meta-llama/Meta-Llama-3-8B-Instruct meta-llama/Meta-Llama-3-70B-Instruct mistralai/Mixtral-8x7B-Instruct-v0.1 lmsys/vicuna-13b-v1.5 mistralai/Mistral-7B-Instruct-v0.3 --output-dir results
python3 -W ignore run.py --models google/flan-t5-xl lmsys/vicuna-13b-v1.5 --output-dir results
