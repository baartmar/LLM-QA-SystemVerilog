module sequence_operators_tb();

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

  sequence grant_1_5_S;
    grant[1] ##20 grant[5];
  endsequence

  sequence grant_2_6_S;
    grant[2] ##2 grant[6];
  endsequence

  grant_1_2_6_5_C: cover property (
    @(posedge clock) grant_2_6_S within grant_1_5_S
  );

  sequence grant_1_6_S;
    grant[1] ##2 grant[6];
  endsequence

  grant_1_6_5_C: cover property (
    @(posedge clock) grant_1_5_S and grant_1_6_S
  );

  grant_1_6or5_C: cover property (
    @(posedge clock) grant_1_5_S or grant_1_6_S
  );

  sequence grant_1_4_5_S;
    grant[1] ##10 grant[4] ##[0:20] grant[5];
  endsequence

  grant_1_4_5_C: cover property (
    @(posedge clock) grant_1_5_S intersect grant_1_4_5_S
  );

  grant_2_skipped_AT: assert property (
    @(posedge clock) not ((!stall && !grant[2] && request[2]) throughout
      (grant[1] ##4 grant[5]))
  );

  first_match_grant_1_4_5_C: cover property (
     @(posedge clock) first_match(grant_1_4_5_S)
  );

  grant_1_4_5_no_stall_C: cover property (
     @(posedge clock) !stall throughout grant_1_4_5_S
  );

  sequence request_6_fell_S;
    !request[6] ##1 request[6][*3] ##1 !request[6];
  endsequence

  request_6_fell_implies_grant_6_AT: assert property (
    @(posedge clock) request_6_fell_S.triggered |-> $past(grant[6], 1)
  );

  request_6_fell_C: cover property (
    @(posedge clock) request_6_fell_S.triggered
  );

endmodule