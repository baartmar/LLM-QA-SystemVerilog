source "/nfs/stak/users/baartmar/hpc-share/LLM-QA-SystemVerilog/.venv/bin/activate"
module load cuda/12.1
export HUGGINGFACE_HUB_CACHE="/nfs/stak/users/baartmar/hpc-share/LLM-QA-SystemVerilog/.cache"
export HF_DATASETS_CACHE="/nfs/stak/users/baartmar/hpc-share/LLM-QA-SystemVerilog/.datasets"
python3 run.py