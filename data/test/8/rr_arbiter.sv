module rr_arbiter #(
  parameter int N_OF_INPUTS = 2
)(
  input                           clk,
  input                           arst,
  input                           update_i,
  input         [N_OF_INPUTS-1:0] req_i,
  output  logic [N_OF_INPUTS-1:0] grant_o
);
  logic [N_OF_INPUTS-1:0] mask_ff, next_mask;
  logic [N_OF_INPUTS-1:0] grant_ff, next_grant;

  always_comb begin
    next_mask  = mask_ff;
    next_grant = grant_ff;
    grant_o    = grant_ff;

    // We only check the inputs during the update == 1
    if (update_i) begin
      next_grant = '0;

      /*verilator coverage_off*/
      // Checking each master against the mask
      for (int i=0; i<N_OF_INPUTS; i++) begin
        if (req_i[i] && mask_ff[i]) begin
          next_grant[i] = 1'b1;
          next_mask[i]  = 1'b0;
          break;
        end
      end

      // If all masters were served
      if ((mask_ff & req_i) == '0) begin
        next_mask = '1;
        for (int i=(N_OF_INPUTS-1); i>=0; i--) begin
          if (req_i[i] == 1'b1) begin
            next_grant[i] = 1'b1;
            next_mask[i]  = 1'b0;
            break;
          end
        end
      end
      /*verilator coverage_on*/
    end
  end

  always_ff @ (posedge clk or posedge arst) begin
    if (arst) begin
      mask_ff  <= '1;
      grant_ff <= '0;
    end
    else begin
      mask_ff  <= next_mask;
      grant_ff <= next_grant;
    end
  end
endmodule