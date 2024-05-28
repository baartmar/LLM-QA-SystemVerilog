module fifo
  #(
    parameter WIDTH,
    parameter DEPTH
    )
   (
    input logic              clk,
    input logic              rst,
    output logic             full,
    input logic              wr_en,
    input logic [WIDTH-1:0]  wr_data,
    output logic             empty, 
    input logic              rd_en,
    output logic [WIDTH-1:0] rd_data  
    );

   localparam int READ_LATENCY = 1;
   
   logic [WIDTH-1:0]         ram[DEPTH];
   logic                     valid_wr, valid_rd;

   localparam int            ADDR_WIDTH = $clog2(DEPTH)+1;
   logic [ADDR_WIDTH-1:0]   wr_addr_r, rd_addr_r;

   always_ff @(posedge clk) begin
      if (valid_wr) ram[wr_addr_r[ADDR_WIDTH-2:0]] <= wr_data;
      rd_data <= ram[rd_addr_r[ADDR_WIDTH-2:0]];      
   end
      
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         rd_addr_r <= '0;
         wr_addr_r <= '0;
      end
      else begin         
         if (valid_wr) wr_addr_r <= wr_addr_r + 1'b1;
         if (valid_rd) rd_addr_r <= rd_addr_r + 1'b1;
      end
   end 
      
   assign valid_wr = wr_en && !full;
   assign valid_rd = rd_en && !empty;

   assign full = rd_addr_r[ADDR_WIDTH-2:0] == wr_addr_r[ADDR_WIDTH-2:0] && rd_addr_r[ADDR_WIDTH-1] != wr_addr_r[ADDR_WIDTH-1];

   assign empty = rd_addr_r == wr_addr_r;
      
endmodule

module fifo_tb;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty; 
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);         
      end

      disable generate_clock;
      $display("Tests Completed.");
   end
      
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   logic [WIDTH-1:0] correct_rd_data;   
   logic [WIDTH-1:0] reference[$];

   // Imitate the functionality of the FIFO with a queue
   always_ff @(posedge clk or posedge rst)
     if (rst) begin
        reference = {};
     end
     else begin
        correct_rd_data = reference[0];       
        
        // Pop the front element on a valid read
        if (rd_en && !empty) begin
           reference = reference[1:$];
        end

        // Push the write data on a valid write.
        if (wr_en && !full) begin
           reference = {reference, wr_data};
        end    
      end
   
   assert property(@(posedge clk) rd_en && !empty |=> rd_data == correct_rd_data);     
         
endmodule