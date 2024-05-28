module add
  #(
    parameter WIDTH
    )
   (
    input logic [WIDTH-1:0]  in0, in1,
    input logic 	     carry_in,
    output logic [WIDTH-1:0] sum,
    output logic 	     carry_out
    );

   assign {carry_out, sum} = in0 + in1 + carry_in;
   
endmodule


module add_tb;

   localparam WIDTH = 16;

   // To achieve 100% coverage for a WIDTH of 16, this parameter had to be
   // increased to ensure that cross coverage has achieved for the input
   // combinations.
   localparam RANDOM_TESTS = 10000;
   //localparam RANDOM_TESTS = 1000;

   localparam ZERO_TESTS = 100;
   localparam MAX_TESTS = 100;
   
   logic [WIDTH-1:0] in0, in1;
   logic [WIDTH-1:0] sum;
   logic             carry_out, carry_in;
    
   add #(.WIDTH(WIDTH)) DUT (.*);

   logic             clk;
   covergroup cg @(posedge clk);
      // Make sure the carry_in is asserted at least 100 times.
      cin : coverpoint carry_in {bins one = {1}; option.at_least = 100;}
      // Make sure the carry out is generated at least 10 times.
      cout : coverpoint carry_out {bins one = {1}; option.at_least = 10;}

      // Make sure that in0 has a 0 and max value tested at least 10 times.
      in0_extremes : coverpoint in0 {
         bins zero = {0};
         bins max_ = {{WIDTH{1'b1}}};
         option.at_least = 10; 
      }
      // Make sure that in1 has a 0 and max value tested at least 10 times.
      in1_extremes : coverpoint in1 {
         bins zero = {0};
         bins max_ = {{WIDTH{1'b1}}};
         option.at_least = 10; 
      }

      // Divide up the input space into 16 bins and make sure all bins are
      // tested at least once.
      in0_full : coverpoint in0 {option.auto_bin_max = 16;}
      in1_full : coverpoint in1 {option.auto_bin_max = 16;}
       
      // Make sure all combinations of input bins are tested at least once.
      in0_cross_in1 : cross in0_full, in1_full;

      // Check to make sure both inputs are 0 or the max value at the same time.
      // It would be more readable to use cover properties here, but if we
      // want this included in the coverage reporting for the group, we need it
      // here.
      in0_in1_eq_0 : coverpoint (in0==0 && in1==0) {bins true = {1'b1};}
      in0_in1_eq_max : coverpoint (in0=={WIDTH{1'b1}} && in1=={WIDTH{1'b1}}) {bins true = {1'b1};}
           
   endgroup

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   cg cg_inst;      
   initial begin
      cg_inst = new();      
      $timeformat(-9, 0, " ns");
      
      // Random tests.
      for (int i=0; i < RANDOM_TESTS; i++) begin
         in0 = $random;
         in1 = $random;
         carry_in = $random;             
         @(posedge clk);
      end

      // in0 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
         in0 = 0;
         in1 = $random;
         carry_in = $random;             
         @(posedge clk);
      end

      // in1 == 0 tests.
      for (int i=0; i < ZERO_TESTS; i++) begin
         in0 = $random;
         in1 = 0;
         carry_in = $random;             
         @(posedge clk);
      end

      // in0 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
         in0 = {WIDTH{1'b1}};
         in1 = $random;
         carry_in = $random;             
         @(posedge clk);
      end

      // in1 == MAX tests.
      for (int i=0; i < MAX_TESTS; i++) begin
         in0 = $random;
         in1 = {WIDTH{1'b1}};
         carry_in = $random;             
         @(posedge clk);
      end

      // Test both inputs at 0 to achieve 100% coverage.
      for (int i=0; i < 2; i++) begin
         in0 = 0;
         in1 = 0;
         carry_in = i;           
         @(posedge clk);
      end

      // Test both inputs with their maximum values to achieve 100% coverage.
      for (int i=0; i < 2; i++) begin
         // Another way of setting all the bits to 1.
         in0 = '1;
         in1 = '1;       
         carry_in = i;   
         @(posedge clk);
      end
            
      $display("Tests completed.");
      $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());      
      disable generate_clock;      
   end

   assert property (@(posedge clk) sum == in0 + in1 + carry_in);
   assert property (@(posedge clk) carry_out == {{1'b0, in0} + in1 + carry_in}[WIDTH]);
   
endmodule