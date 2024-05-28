module sampled_value_functions_tb();

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

  sequence gnt4_in_31_cycles_S1;
    $rose(request[4]) ##[0:31] grant[4];
  endsequence;

  gnt4_in_31_cycles_C1: cover property (
    @(posedge clock) (gnt4_in_31_cycles_S1)
  );

  property req4_wait_for_grant_P;
    request[4] && !grant[4] |-> !$fell(request[4]);
  endproperty;

  gnt4_in_31_cycles_AS1: assume property (
    @(posedge clock) (req4_wait_for_grant_P)
  );

  req4_stable_on_stall_AT1: assert property (
    @(posedge clock) disable iff (cycle_after_reset) (
      stall && request[4] |-> ##1 $stable(request[4])
    )
  );

  req4_stable_on_stall_AT2: assert property (
    @(posedge clock) disable iff (cycle_after_reset) (
      stall && request[4] |-> ##1 !$changed(request[4])
    )
  );

  req_stable_when_no_gnt_AS1: assume property (
    @(posedge clock) disable iff (cycle_after_reset) (
      &((~($past(request) & (~$past(grant)))) | request)
    )
  );

endmodule