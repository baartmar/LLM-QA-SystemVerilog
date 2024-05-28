module intro_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

  wire stall = 1'b0;

  rr_arbiter #(.CLIENTS(32)) dut (
                  .request (request),
                  .grant   (grant),
                  .stall   (stall),
                  .clock   (clock),
                  .reset   (reset));

  sequence gnt4_in_31_cycles_S;
    ##[0:31] grant[4];
  endsequence;

  property gnt4_in_31_cycles_P0;
    request[4] |-> gnt4_in_31_cycles_S;
  endproperty;

  property gnt4_in_31_cycles_P1;
    request[4] |-> ##[0:31] grant[4];
  endproperty;

  gnt4_in_31_cycles_AT: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P0)
  );

  generate
    for (genvar i=0; i<CLIENTS; i++) begin
      hold_request_till_grant: assume property (
        @(posedge clock) (
          request[i] && !grant[i] |-> ##1 request[i]
        )
      );
    end
  endgenerate

  sequence gnt5_received_in_31_cycles_S;
    @(posedge clock) !request[5] ##1 request[5] ##0 (!grant[5])[*31] ##1 grant[5];
  endsequence;

  gnt5_received_in_31_cycles_C: cover property (gnt5_received_in_31_cycles_S);

  sequence gnt5_received_in_32_cycles_Fail_S;
    @(posedge clock) !request[5] ##1 request[5] ##0 (!grant[5])[*32] ##1 grant[5];
  endsequence;

  gnt5_received_in_32_cycles_Fail_C: cover property (gnt5_received_in_32_cycles_Fail_S);

endmodule