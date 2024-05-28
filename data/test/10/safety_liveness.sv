module safety_vs_liveness_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

  rr_arbiter #(.CLIENTS(32)) dut (
                  .request (request),
                  .grant   (grant),
                  .stall   (stall),
                  .clock   (clock),
                  .reset   (reset));

  logic cycle_after_reset;
  always @(posedge clock) begin
    if (reset)
      cycle_after_reset <= 1'b1;
    else
      cycle_after_reset <= 1'b0;
  end

  req_stable_AS1: assume property (
    @(posedge clock) disable iff (cycle_after_reset) (
      &((~($past(request) & (~$past(grant)))) | request)
    )
  );

  grant_within_32_AT0: assert property (
    @(posedge clock) request[4] |-> ##[0:31] grant[4]
  );

  grant_within_32_AT1: assert property (
    @(posedge clock) request[4] |-> s_eventually grant[4]
  );


  grant_within_32_AT2: assert property (
    @(posedge clock) request[4] |-> ##[0:$] grant[4]
  );

  grant_within_32_AT3: assert property (
    @(posedge clock) request[4] |-> strong(##[0:$] grant[4])
  );

endmodule
