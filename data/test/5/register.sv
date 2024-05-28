// Greg Stitt
// University of Florida

// Module: register
// Description: Implements a register with an active high, asynchronous reset
// and an enable signal.

module register
  #(
    parameter WIDTH
    )
   (
    input logic              clk,
    input logic              rst,
    input logic              en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst)
        out <= '0;
      else if (en)
        out <= in;      
   end 
   
endmodule

// Module: register_tb2
// Description: This testbench extends the previous one to handle the enable
// and to cover more tests.

module register_tb2;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;

   // Only used for one of the assertion alternatives.
   logic             output_check_en = 1'b0, first_en = 1'b0;
      
   register #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);

         // Only used for one of the assertion examples. Probably not
         // recommended due to the complexity.
         // If we've seen the first enable, then we can enable the output 
         // checker assertion.
         if (first_en) output_check_en = 1'b1;
         // Flag that we've seen the first enable.
         if (en) first_en = 1'b1;         
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // For the enable, we can use the same strategy as the FF example.
   // Verify output when enable is asserted.
   assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));

   // Verify output when enable isn't asserted. 
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));
   
   always @(rst) #1 assert(out == '0);  
endmodule