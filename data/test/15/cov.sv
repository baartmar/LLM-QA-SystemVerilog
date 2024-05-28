class MyTest;
  // defines a user-defined enumeration type
  typedef enum logic {front, back} face_t;

  // declares member fields using native and user-defined types
  logic [1:0]  dat1;
  logic [1:0]  dat2;
  rand face_t face;

  /* covergroup: cg
     This user-defined covergroup defines coverpoints, associated bins and
     covergroup instance specific option
   */
  covergroup cg;
    /* Coverage information for the instance is saved in the coverage database
       and included in the coverage report.
     */ 
    option.per_instance = 1;

    /* "bin1" is an explicit coverage point defined for member field "dat1"
       with two bins specified for specific value ranges 
     */
    bin1: coverpoint dat1 {
      bins s = {[0:1]};
      bins l = {[2:3]};
    }

    /* "bin2" is an explicit coverage point defined for member field "dat2"
       with two bins specified for specific value ranges
     */
    bin2: coverpoint dat2 {
      bins s = {[0:1]};
      bins l = {[2:3]};
    }

    /* "bins_cnd1" is an explicit coverage point defined for member field 
       "dat1" otherwise ignored if the guard expression evaluates to false.
       A bin for each possible value is automatically created by SystemVerilog.
     */
    bins_cnd1: coverpoint dat1 iff (face == front);

    /* "bins_cnd2" is an explicit coverage point defined for member field 
       "dat1" otherwise ignored if the guard expression evaluates to false.
       Bin zero for value 0 is ignored if the guard expression evaluates false.
       Bin int_num is an array of bins specified for each value from the range
       expression with a "$" upper limit, which means the extremum range value.
     */
    bins_cnd2: coverpoint dat1 {
      bins zero = {0} iff (face == front);
      bins int_num[] = {[1:$]};
    }

    /* "all_dats" is a labeled cross coverage of implicit coverpoints "dat1"
       and "dat2". SystemVerilog automatically creates each possible cross 
       of the coverpoints involved.
     */
    all_dats: cross dat1, dat2;                 // All combinations of dat1 x dat2, that is 16 combinations.

    /* "all_bins" is a labeled cross coverage of explicit coverpoints "bin1"
       and "bin2". SystemVerilog automatically creates each possible cross 
       of the coverpoints involved.
     */
    all_bins: cross bin1, bin2;                 // All combinations of bin1 x bin2, that is 4 combinations.

    /* "dat_bin" is a labeled cross coverage of explicit coverpoint "bin2" and
       implicit coverpoint "dat1". SystemVerilog automatically creates each
       possible cross of the coverpoints involved.
     */
    dat_bin: cross dat1, bin2;                  // Combination of variable x bin

    /* "useOfBinsof" is a labeled cross coverage of explicit coverpoints "bin1"
       and "bin2" with a set of specific bins using the "binsof()" method to
       select scope from bins specified earlier and an automatically generated
       unspecified bin.
     */
    useOfBinsof: cross bin1, bin2 {
      bins bin1_is_s = binsof(bin1.s);                                         // <s, s>, <s.l>
      bins bin_s_and_s = binsof(bin1.s) && binsof(bin2.s);                     // <s, s>
      bins bin_s_or_s  = binsof(bin1.s) || binsof(bin2.s);                     // <s, s>, <s, l>, <l, s>
      bins bin_not_l   = !binsof(bin1.l);                                      // <s, s>, <s, l>
      bins bin_paren   = (binsof(bin1.s) || binsof(bin2.s)) && binsof(bin2.l); // <s, l>
      // Bins for the combinations that are not specified will be generated automatically.
      // <l, l>
    }

    /* "cbins_v" is a labeled cross coverage of implicit coverpoints "dat1"
       and "dat2" with a specific bin using the "binsof()" and "intersect()" 
       methods to select scope from bins specified earlier against a value
       range, and automatically generated unspecified bins.
     */
    cbins_v: cross dat1, dat2 {
      bins bin1_0 = binsof(dat1) intersect {[0:2]}; // A bin covers all combinations below:
                                                    // <0, 0>, <0, 1>, <0, 2>, <0, 3>
                                                    // <1, 0>, <1, 1>, <1, 2>, <1, 3>
                                                    // <2, 0>, <2, 1>, <2, 2>, <2, 3>
    // Bins will be automatically created for the combinations below
    // <3, 0>, <3, 1>, <3, 2>, <3, 3>
    }

    /* "cbins_b_0" is a labeled cross coverage of explicit coverpoints "bin1"
       and "bin2" with a specific bin using the "binsof()" and "intersect()" 
       methods to select scope from bins specified earlier against a value 
       range, and automatically generated unspecified bins.
     */
    cbins_b_0: cross bin1, bin2 {
      bins bin0 = binsof(bin1) intersect {0}; // Equivalent to binsof(bin1.s)
                                              // <s, s>, <s, l>
      // <l, s>, <l, l>
    }

    /* "cbins_b_1" is an equivalent of "cbins_b_0" due to specific coverpoint
       bins' value range scoping.
     */
    cbins_b_1: cross bin1, bin2 {
      bins bin0 = binsof(bin1) intersect {[0:1]}; // Equivalent to binsof(bin1.s)
                                                  // <s, s>, <s, l>
      // <l, s>, <l, l>
    }

    /* "cbins_b_2" is a labeled cross coverage of explicit coverpoints "bin1"
       and "bin2" with a specific bin using the "binsof()" and "intersect()" 
       methods to select scope from bins specified earlier against a value 
       range, and no unspecified bins.
     */
    cbins_b_2: cross bin1, bin2 {
      bins bin0 = binsof(bin1) intersect {[0:2]}; // Equivalent to binsof(bin1.s) || binsof(bin1.l)
                                                  // <s, s>, <s, l>, <l, s>, <l, l>
      // No auto bin
    }

    /* "useOfIgn" is a labeled cross coverage of implicit coverpoints "dat1"
       and "dat2" with a specific ignore bin selected with the "binsof()" and 
       "intersect()" methods, and automatically generated unspecified legal 
       bins.
     */
    useOfIgn: cross dat1, dat2 {
      ignore_bins ign = binsof (dat1) intersect {[0:2]} ||   //<0, 0>, <0, 1>, <0, 2>, <0, 3>,
                        binsof (dat2) intersect {[0:1]};     //<1, 0>, <1, 1>, <1, 2>, <1, 3>,
                                                             //<2, 0>, <2, 1>, <2, 2>, <2, 3>,
                                                             //<3, 0>, <3, 1>
      // Automatically Created cross bins
      // <3, 2>, <3, 3>
    }

    /* "cond1" is a labeled cross coverage of explicit coverpoints "bin1"
       and "bin2" otherwise ignored if the guard expression evaluates to 
       false.
     */
    cond1: cross bin1, bin2 iff (face == front); // Collect coverage only when face == front

    /* "cond2" is a labeled cross coverage of explicit coverpoints "bin1"
       and "bin2" otherwise ignored if the guard expression evaluates to false.
       Bin "bin1s" is a specific bin with a guard expression while 
       automatically generated unspecified bins are collected unconditionally.
     */
    cond2: cross bin1, bin2 {
      bins bin1s = binsof(bin1.s) iff (face == front); // Collect coverage only when face == front
      // Other bins are always collected
    }

    /* "cond3" is a labeled cross coverage of explicit coverpoint "bins_cnd1"
       and implicit coverpoint "dat2". The guard condition of the former
       applies.
     */
    cond3: cross bins_cnd1, dat2; //bins_cnd1 has iff

    /* "cond4" is a labeled cross coverage of explicit coverpoint "bins_cnd2"
       and implicit coverpoint "dat2". The guard condition of the former
       applies.
     */
    cond4: cross bins_cnd2, dat2; //bins_cnd2 has a bin with iff
  endgroup

  // SystemVerilog class object constructor.
  function new();
    // No name is passed to the instance of the covergroup cg
    cg = new;
  endfunction

  // User-defined function "run()"
  function void run();
    // Nested loop to sweep all possible values of each member field
    for (int i = 0; i < 2**$size(dat1); i++) begin
      for (int j = 0; j < 2**$size(dat2); j++) begin
        for (int k = 0; k < 2**$size(face); k++) begin
          /* Program Sequence - 2. 
             Assign current loop variable values to class member fields
           */
          dat1 = i;
          dat2 = j;
          face = face_t'(k);
          cg.sample();
        end
      end
    end
  endfunction
endclass

/* program: top
   This is a simple way to instantiate a SystemVerilog class object and
   invoke any of its methods.
*/
program top;
  initial begin
    // Instance of "MyTest" class object
    MyTest myTest;

    // "MyTest" class object constructor
    myTest = new;

    myTest.run();
  end
endprogram