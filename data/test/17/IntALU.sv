module IntALU
(
    input wire clk,
    input wire en,
    input wire rst,

    input wire IN_wbStall,
    input EX_UOp IN_uop,
    input IN_invalidate,
    input SqN IN_invalidateSqN,
    
    output wire OUT_wbReq,

    output BranchProv OUT_branch,
    output BTUpdate OUT_btUpdate,
    
    output ZCForward OUT_zcFwd,

    output RES_UOp OUT_uop
);

wire[31:0] srcA = IN_uop.srcA;
wire[31:0] srcB = IN_uop.srcB;
wire[31:0] imm = IN_uop.imm;

assign OUT_wbReq = IN_uop.valid && en;

reg[31:0] resC;
Flags flags;

assign OUT_zcFwd.result = resC;
assign OUT_zcFwd.tag = IN_uop.tagDst;
assign OUT_zcFwd.valid = IN_uop.valid && en && !IN_uop.tagDst[$bits(Tag)-1];

wire[5:0] resLzTz;

reg[31:0] srcAbitRev;
always_comb begin
    for (integer i = 0; i < 32; i=i+1)
        srcAbitRev[i] = srcA[31-i];
end
LZCnt lzc (
    .in(IN_uop.opcode == INT_CLZ ? srcA : srcAbitRev),
    .out(resLzTz)
);

wire[5:0] resPopCnt;
PopCnt popc
(
    .a(IN_uop.srcA),
    .res(resPopCnt)
);

wire lessThan = ($signed(srcA) < $signed(srcB));
wire lessThanU = (srcA < srcB);

wire[31:0] pcPlus2 = IN_uop.pc + 2;
wire[31:0] pcPlus4 = IN_uop.pc + 4;

always_comb begin
    case (IN_uop.opcode)
        INT_AUIPC: resC = IN_uop.pc + imm;
        ATOMIC_AMOADD_W, INT_ADD: resC = srcA + srcB;
        ATOMIC_AMOXOR_W, INT_XOR: resC = srcA ^ srcB;
        ATOMIC_AMOOR_W, INT_OR: resC = srcA | srcB;
        ATOMIC_AMOAND_W, INT_AND: resC = srcA & srcB;
        ATOMIC_AMOMAX_W, INT_MAX: resC = lessThan ? srcB : srcA;
        ATOMIC_AMOMAXU_W, INT_MAXU: resC = lessThanU ? srcB : srcA;
        ATOMIC_AMOMIN_W, INT_MIN: resC = lessThan ? srcA : srcB;
        ATOMIC_AMOMINU_W, INT_MINU: resC = lessThanU ? srcA : srcB;
        INT_SLL: resC = srcA << srcB[4:0];
        INT_SRL: resC = srcA >> srcB[4:0];
        INT_SLT: resC = {31'b0, lessThan};
        INT_SLTU: resC = {31'b0, lessThanU};
        INT_SUB: resC = srcA - srcB;
        INT_SRA: resC = $signed(srcA) >>> srcB[4:0];
        INT_LUI: resC = srcB;
        INT_V_JR,
        INT_V_RET,
        INT_V_JALR,
        INT_JAL: resC = (IN_uop.compressed ? pcPlus2 : pcPlus4);
        INT_SYS: resC = 32'bx;
        INT_SH1ADD: resC = srcB + (srcA << 1);
        INT_SH2ADD: resC = srcB + (srcA << 2);
        INT_SH3ADD: resC = srcB + (srcA << 3);
        INT_ANDN: resC = srcA & (~srcB);
        INT_ORN: resC = srcA | (~srcB);
        INT_XNOR: resC = srcA ^ (~srcB);
        INT_SE_B: resC = {{24{srcA[7]}}, srcA[7:0]};
        INT_SE_H: resC = {{16{srcA[15]}}, srcA[15:0]};
        INT_ZE_H: resC = {16'b0, srcA[15:0]};
        INT_CLZ, 
        INT_CTZ: resC = {26'b0, resLzTz};
        INT_CPOP: resC = {26'b0, resPopCnt};
        INT_ORC_B: resC = {{{4'd8}{|srcA[31:24]}}, {{4'd8}{|srcA[23:16]}}, {{4'd8}{|srcA[15:8]}}, {{4'd8}{|srcA[7:0]}}};
        INT_REV8: resC = {srcA[7:0], srcA[15:8], srcA[23:16], srcA[31:24]};
        INT_FSGNJ_S:  resC = {srcB[31], srcA[30:0]};
        INT_FSGNJN_S: resC = {~srcB[31], srcA[30:0]};
        INT_FSGNJX_S: resC = {srcA[31] ^ srcB[31], srcA[30:0]};
        default: resC = 32'bx;
    endcase
    
    case (IN_uop.opcode)
        INT_SYS: flags = Flags'(imm[3:0]);
        default: flags = FLAGS_NONE;
    endcase
end 


reg isBranch;
reg branchTaken;

always_comb begin
    case (IN_uop.opcode)
        INT_JAL: branchTaken = 1;
        INT_BEQ: branchTaken = (srcA == srcB);
        INT_BNE: branchTaken = (srcA != srcB);
        INT_BLT: branchTaken = lessThan;
        INT_BGE: branchTaken = !lessThan;
        INT_BLTU: branchTaken = lessThanU;
        INT_BGEU: branchTaken = !lessThanU;
        default: branchTaken = 0;
    endcase
    
    isBranch =
        (IN_uop.opcode == INT_BEQ ||
        IN_uop.opcode == INT_BNE ||
        IN_uop.opcode == INT_BLT ||
        IN_uop.opcode == INT_BGE ||
        IN_uop.opcode == INT_BLTU ||
        IN_uop.opcode == INT_BGEU);
end

reg indBranchCorrect;
reg[31:0] indBranchDst;
always_comb begin
    indBranchCorrect = 'x;
    indBranchDst = 'x;
    case (IN_uop.opcode)
        INT_V_RET: begin
            indBranchDst = srcA;
            indBranchDst[0] = 0;
            indBranchCorrect = (indBranchDst[31:1] == srcB[31:1]);
        end
        INT_V_JALR,
        INT_V_JR: begin
            indBranchDst = (srcA + {{20{imm[11]}}, imm[11:0]});
            indBranchDst[0] = 0;
            indBranchCorrect = (indBranchDst[31:1] == srcB[31:1]);
        end
        default: ;
    endcase
end

wire[31:0] finalHalfwPC = IN_uop.compressed ? IN_uop.pc : pcPlus2;

always_ff@(posedge clk) begin
    
    OUT_uop <= 'x;
    OUT_branch <= 'x;
    OUT_btUpdate <= 'x;
    OUT_uop.valid <= 0;
    OUT_branch.taken <= 0;
    OUT_btUpdate.valid <= 0;

    if (!rst) begin
        if (IN_uop.valid && en && !IN_wbStall && (!IN_invalidate || $signed(IN_uop.sqN - IN_invalidateSqN) <= 0)) begin
            OUT_branch.sqN <= IN_uop.sqN;
            OUT_branch.loadSqN <= IN_uop.loadSqN;
            OUT_branch.storeSqN <= IN_uop.storeSqN;
            
            OUT_btUpdate.valid <= 0;
            OUT_branch.taken <= 0;
            OUT_branch.flush <= 0;
            
            OUT_branch.fetchID <= IN_uop.fetchID;
            OUT_branch.histAct <= HIST_NONE;
            OUT_branch.retAct <= RET_NONE;
            
            if (isBranch) begin
                // Send branch target to BTB if unknown.
                if (branchTaken && !IN_uop.bpi.predicted) begin
                    // Uncompressed branches are predicted only when their second halfword is fetched
                    OUT_btUpdate.src <= finalHalfwPC;
                    OUT_btUpdate.fetchStartOffs <= IN_uop.fetchStartOffs;
                    OUT_btUpdate.multiple <= (finalHalfwPC[1+:$bits(FetchOff_t)] > IN_uop.fetchPredOffs);
                    OUT_btUpdate.multipleOffs <= IN_uop.fetchPredOffs + 1;
                    OUT_btUpdate.isJump <= 0;
                    OUT_btUpdate.isCall <= 0;
                    OUT_btUpdate.compressed <= IN_uop.compressed;
                    OUT_btUpdate.clean <= 0;
                    OUT_btUpdate.valid <= 1;
                end
                if (branchTaken != IN_uop.bpi.taken && IN_uop.opcode != INT_JAL) begin
                    if (branchTaken) begin
                        OUT_branch.dstPC <= (IN_uop.pc + {{19{imm[12]}}, imm[12:0]});
                        OUT_btUpdate.dst <= (IN_uop.pc + {{19{imm[12]}}, imm[12:0]});
                    end
                    else if (IN_uop.compressed) begin
                        OUT_branch.dstPC <= pcPlus2;
                        OUT_btUpdate.dst <= pcPlus2;
                    end
                    else begin
                        OUT_branch.dstPC <= pcPlus4;
                        OUT_btUpdate.dst <= pcPlus4;
                    end
                    OUT_branch.taken <= 1;
                    
                    // if predicted but wrong, correct existing history bit
                    if (IN_uop.bpi.predicted)
                        OUT_branch.histAct <= branchTaken ? HIST_WRITE_1 : HIST_WRITE_0;
                    // else append to history
                    else begin
                        assert(branchTaken);
                        OUT_branch.histAct <= HIST_APPEND_1;
                    end
                end
            end
            // Check speculated return address
            else if (IN_uop.opcode == INT_V_RET || IN_uop.opcode == INT_V_JALR || IN_uop.opcode == INT_V_JR) begin
                if (!indBranchCorrect) begin
                    OUT_branch.dstPC <= indBranchDst;
                    OUT_branch.taken <= 1;
                    
                    if (IN_uop.opcode == INT_V_RET)
                        OUT_branch.retAct <= RET_POP;
                    if (IN_uop.opcode == INT_V_JALR)
                        OUT_branch.retAct <= RET_PUSH;
                    
                    if (IN_uop.opcode == INT_V_JALR || IN_uop.opcode == INT_V_JR) begin
                        OUT_btUpdate.src <= finalHalfwPC;
                        OUT_btUpdate.fetchStartOffs <= IN_uop.fetchStartOffs;
                        OUT_btUpdate.multiple <= (finalHalfwPC[1+:$bits(FetchOff_t)] > IN_uop.fetchPredOffs);
                        OUT_btUpdate.multipleOffs <= IN_uop.fetchPredOffs + 1;
                        OUT_btUpdate.dst <= indBranchDst;
                        OUT_btUpdate.isJump <= 1;
                        OUT_btUpdate.isCall <= (IN_uop.opcode == INT_V_JALR);
                        OUT_btUpdate.compressed <= IN_uop.compressed;
                        OUT_btUpdate.clean <= 0;
                        OUT_btUpdate.valid <= 1;
                    end
                end
            end

            OUT_uop.result <= resC;
            OUT_uop.storeSqN <= IN_uop.storeSqN;
            OUT_uop.tagDst <= IN_uop.tagDst;
            OUT_uop.sqN <= IN_uop.sqN;
            // atomics are committed by the store port, not the int port
            OUT_uop.doNotCommit <= (IN_uop.opcode >= ATOMIC_AMOADD_W);
            
            if (isBranch && IN_uop.bpi.predicted)
                OUT_uop.flags <= branchTaken ? FLAGS_PRED_TAKEN : FLAGS_PRED_NTAKEN;
            else if (isBranch)
                OUT_uop.flags <= FLAGS_BRANCH;
            else
                OUT_uop.flags <= flags;
            
            OUT_uop.valid <= 1;
        end
    end
end
endmodule