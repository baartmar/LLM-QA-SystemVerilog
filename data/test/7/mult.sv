module mult1
  #(
    parameter INPUT_WIDTH,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );
   
   always_comb begin
      if (IS_SIGNED) 
      	product = signed'(in0) * signed'(in1);                
      else
	product = in0 * in1;
      
   end     
endmodule // mult1

module mult2
  #(
    parameter INPUT_WIDTH,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );

   generate
      if (IS_SIGNED) begin : l_is_signed
	 assign product = signed'(in0) * signed'(in1);                
      end
      else begin : l_is_unsigned
	 assign product = in0 * in1;
      end
   endgenerate  
endmodule

module mult3
  #(
    parameter INPUT_WIDTH,
    parameter logic IS_SIGNED = 1'b0
    )
   (
    input logic [INPUT_WIDTH-1:0]    in0, in1,
    output logic [INPUT_WIDTH*2-1:0] product
    );

   assign product = l_mult_func.multiply(in0, in1);

   generate
      case (IS_SIGNED)
	1'b0: begin: l_mult_func
	   function automatic [INPUT_WIDTH*2-1:0] multiply(input [$bits(in0)-1:0] x, y);
	      
	      return x * y;
	   endfunction
	end
	1'b1: begin: l_mult_func
	     function automatic [INPUT_WIDTH*2-1:0] multiply(input [$bits(in0)-1:0] x, y);
		
		return signed'(x) * signed'(y);
	     endfunction
	end
      endcase
   endgenerate  
endmodule