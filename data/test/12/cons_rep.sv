module cons_rep_operator_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

  wire stall = 0;

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

  req4_req5_gnt4_d3_gnt5_C: cover property (
     @(posedge clock) request[4] ##0 (!grant[4])[*3] ##1 grant[4]
  );

  req4_req5_gnt4_d1_3_gnt5_C: cover property (
     @(posedge clock) request[4] ##0 (!grant[4])[*1:3] ##1 grant[4]
  );

  req4_and_not_gnt4_for_upto_cycle30_AT: assert property (
     @(posedge clock) request[4] &&!grant[4] |-> ##1 (!grant[4])[*0:29]
  );

  req4_and_not_gnt4_within_30_AT_FAIL: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:29] ##1 grant[4]
  );

  req4_and_not_gnt4_for_upto_31_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:30]
  );

  req4_and_not_gnt4_within_31_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:31] ##1 grant[4]
  );

  req4_and_not_gnt4_for_upto_32_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:31]
  );

  req4_and_not_gnt4_within_32_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:31] ##1 grant[4]
  );

  req4_and_not_gnt4_for_31_AT: assert property (
     @(posedge clock) request[4] |-> not ((!grant[4])[*32])
  );

  gnt4_within_32_AT1: assert property (
    request[4] |-> (!grant[4])[*0:31] ##1 grant[4]
  );

  gnt4_within_32_AT2: assert property (
    request[4] |-> ##[0:31] grant[4]
  );
endmodule
