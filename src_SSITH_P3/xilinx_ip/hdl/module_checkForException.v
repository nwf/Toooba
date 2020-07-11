//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Fri Jul 10 21:05:22 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// checkForException              O    14
// checkForException_dInst        I   145
// checkForException_regs         I    27
// checkForException_csrState     I    15
// checkForException_pcc          I   129
// checkForException_fourByteInst  I     1
//
// Combinational paths from inputs to outputs:
//   (checkForException_dInst,
//    checkForException_regs,
//    checkForException_csrState,
//    checkForException_pcc,
//    checkForException_fourByteInst) -> checkForException
//
//

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module module_checkForException(checkForException_dInst,
				checkForException_regs,
				checkForException_csrState,
				checkForException_pcc,
				checkForException_fourByteInst,
				checkForException);
  // value method checkForException
  input  [144 : 0] checkForException_dInst;
  input  [26 : 0] checkForException_regs;
  input  [14 : 0] checkForException_csrState;
  input  [128 : 0] checkForException_pcc;
  input  checkForException_fourByteInst;
  output [13 : 0] checkForException;

  // signals for module outputs
  wire [13 : 0] checkForException;

  // remaining internal signals
  reg [5 : 0] CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4;
  reg [4 : 0] CASE_checkForException_dInst_BITS_37_TO_33_0_c_ETC__q2;
  reg [2 : 0] CASE_checkForException_csrState_BITS_14_TO_12__ETC__q3;
  reg CASE_checkForException_dInst_BITS_144_TO_140_2_ETC__q5,
      IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566;
  wire [63 : 0] memCap_address__h637, x__h443, x__h997;
  wire [31 : 0] imm__h1512;
  wire [18 : 0] INV_checkForException_pcc_BITS_108_TO_90__q1;
  wire [13 : 0] b_base__h929,
		cr_addrBits__h111,
		cr_addrBits__h561,
		x__h960,
		y__h1054;
  wire [12 : 0] IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d719;
  wire [11 : 0] IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d18,
		b_top__h928,
		csr__h1509,
		inc__h652;
  wire [5 : 0] x__h1035;
  wire [4 : 0] IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d702,
	       IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d704,
	       IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d705,
	       rs1__h1511;
  wire [2 : 0] IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545,
	       repBound__h535,
	       tb__h532,
	       tmp_expBotHalf__h991,
	       tmp_expTopHalf__h989;
  wire [1 : 0] carry_out__h594,
	       impliedTopBits__h596,
	       len_correction__h595,
	       x__h617;
  wire IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d51,
       IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d573,
       IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d577,
       IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d69,
       IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d695,
       IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d80,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d39,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d40,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d42,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d46,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d47,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d48,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d60,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d61,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d62,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d65,
       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d66,
       IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d681,
       IF_checkForException_dInst_BIT_38_70_THEN_chec_ETC___d562,
       NOT_checkForException_dInst_BITS_139_TO_137_02_ETC___d594,
       NOT_checkForException_dInst_BITS_139_TO_137_02_ETC___d678,
       NOT_checkForException_dInst_BIT_51_22_68_OR_NO_ETC___d417,
       NOT_checkForException_pcc_BIT_122_8_9_AND_NOT__ETC___d468,
       checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d266,
       checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d493,
       checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d515,
       checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d264,
       checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d406;

  // value method checkForException
  assign checkForException =
	     { IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d80 ||
	       checkForException_dInst[144:140] == 5'd22 ||
	       checkForException_dInst[144:140] == 5'd23 ||
	       IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566,
	       IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d719 } ;

  // remaining internal signals
  assign IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d702 =
	     (IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d573 &&
	      IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d577 &&
	      !checkForException_pcc[113]) ?
	       5'd17 :
	       ((IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d573 &&
		 IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d577 &&
		 checkForException_pcc[113] &&
		 INV_checkForException_pcc_BITS_108_TO_90__q1[18:1] ==
		 18'd262143 &&
		 checkForException_pcc[128]) ?
		  5'd24 :
		  5'd27) ;
  assign IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d704 =
	     IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d695 ?
	       5'd2 :
	       ((IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d573 &&
		 IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d577 &&
		 checkForException_pcc[113] &&
		 INV_checkForException_pcc_BITS_108_TO_90__q1[18:1] !=
		 18'd262143) ?
		  5'd3 :
		  IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d702) ;
  assign IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d705 =
	     (IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d80 &&
	      (IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d51 ||
	       IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d69)) ?
	       5'd1 :
	       IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d704 ;
  assign IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d719 =
	     (IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d80 ||
	      checkForException_dInst[144:140] != 5'd22 &&
	      checkForException_dInst[144:140] != 5'd23 &&
	      CASE_checkForException_dInst_BITS_144_TO_140_2_ETC__q5) ?
	       { 8'd32,
		 IF_IF_IF_INV_checkForException_pcc_BITS_108_TO_ETC___d705 } :
	       { 8'd106,
		 ((checkForException_dInst[144:140] == 5'd22) ?
		    checkForException_csrState[10:9] != 2'd0 &&
		    checkForException_csrState[10:9] != 2'd1 &&
		    checkForException_csrState[10:9] != 2'd3 :
		    checkForException_dInst[144:140] != 5'd23) ?
		   5'd2 :
		   ((checkForException_dInst[144:140] == 5'd23) ?
		      5'd3 :
		      ((checkForException_dInst[144:140] == 5'd22 &&
			checkForException_csrState[10:9] == 2'd0) ?
			 5'd8 :
			 ((checkForException_dInst[144:140] == 5'd22 &&
			   checkForException_csrState[10:9] == 2'd1) ?
			    5'd9 :
			    ((checkForException_dInst[144:140] == 5'd22 &&
			      checkForException_csrState[10:9] == 2'd3) ?
			       5'd11 :
			       5'd28)))) } ;
  assign IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d51 =
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d40 ?
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d42 :
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29) ||
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d47 ?
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d48 :
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d39) ;
  assign IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d573 =
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d40 ?
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d42 :
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29) &&
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d47 ?
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d48 :
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d39) ;
  assign IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d577 =
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d61 ?
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d62 :
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29) &&
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d65 ?
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d66 :
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d60) ;
  assign IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d69 =
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d61 ?
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d62 :
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29) ||
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d65 ?
		IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d66 :
		!IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d60) ;
  assign IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d695 =
	     (IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d51 ||
	      IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d69 ||
	      !checkForException_pcc[128]) &&
	     IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d573 &&
	     IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d577 &&
	     checkForException_pcc[113] &&
	     INV_checkForException_pcc_BITS_108_TO_90__q1[18:1] ==
	     18'd262143 ;
  assign IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d80 =
	     IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d51 ||
	     IF_IF_INV_checkForException_pcc_BITS_108_TO_90_ETC___d69 ||
	     !checkForException_pcc[113] ||
	     INV_checkForException_pcc_BITS_108_TO_90__q1[18:1] !=
	     18'd262143 ||
	     !checkForException_pcc[128] ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d18 =
	     INV_checkForException_pcc_BITS_108_TO_90__q1[0] ?
	       { checkForException_pcc[89:81], 3'd0 } :
	       b_top__h928 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29 =
	     tb__h532 < repBound__h535 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d39 =
	     cr_addrBits__h111[13:11] < repBound__h535 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d40 =
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29 ==
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d39 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d42 =
	     cr_addrBits__h111 <= y__h1054 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d46 =
	     x__h960[13:11] < repBound__h535 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d47 =
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d46 ==
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d39 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d48 =
	     cr_addrBits__h111 < x__h960 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d60 =
	     cr_addrBits__h561[13:11] < repBound__h535 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d61 =
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d29 ==
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d60 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d62 =
	     cr_addrBits__h561 <= y__h1054 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d65 =
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d46 ==
	     IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d60 ;
  assign IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d66 =
	     cr_addrBits__h561 < x__h960 ;
  assign IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545 =
	     (checkForException_dInst[113:111] != 3'd0 &&
	      checkForException_dInst[113:111] != 3'd1 &&
	      checkForException_dInst[113:111] != 3'd2 &&
	      checkForException_dInst[113:111] != 3'd3 &&
	      checkForException_dInst[113:111] != 3'd4) ?
	       CASE_checkForException_csrState_BITS_14_TO_12__ETC__q3 :
	       checkForException_dInst[113:111] ;
  assign IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d681 =
	     (checkForException_dInst[144:140] == 5'd17) ?
	       NOT_checkForException_dInst_BITS_139_TO_137_02_ETC___d678 &&
	       !checkForException_pcc[122] &&
	       NOT_checkForException_dInst_BIT_51_22_68_OR_NO_ETC___d417 :
	       checkForException_dInst[38] &&
	       !checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d493 &&
	       (checkForException_dInst[37:33] == 5'd0 ||
		checkForException_dInst[37:33] == 5'd1 ||
		checkForException_dInst[37:33] == 5'd12 ||
		checkForException_dInst[37:33] == 5'd13 ||
		checkForException_dInst[37:33] == 5'd14 ||
		checkForException_dInst[37:33] == 5'd15 ||
		checkForException_dInst[37:33] == 5'd28 ||
		checkForException_dInst[37:33] == 5'd29 ||
		checkForException_dInst[37:33] == 5'd30 ||
		checkForException_dInst[37:33] == 5'd31) ;
  assign IF_checkForException_dInst_BIT_38_70_THEN_chec_ETC___d562 =
	     checkForException_dInst[38] ?
	       checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d515 :
	       checkForException_dInst[144:140] == 5'd16 &&
	       (checkForException_dInst[139:137] != 3'd4 ||
		IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545 !=
		3'd0 &&
		IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545 !=
		3'd1 &&
		IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545 !=
		3'd2 &&
		IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545 !=
		3'd3 &&
		IF_NOT_checkForException_dInst_BITS_113_TO_111_ETC___d545 !=
		3'd4) ;
  assign INV_checkForException_pcc_BITS_108_TO_90__q1 =
	     ~checkForException_pcc[108:90] ;
  assign NOT_checkForException_dInst_BITS_139_TO_137_02_ETC___d594 =
	     (checkForException_dInst[139:137] != 3'd0 ||
	      checkForException_dInst[114:110] != 5'd15) &&
	     rs1__h1511 == 5'd0 &&
	     imm__h1512 == 32'd0 ||
	     csr__h1509[11:10] != 2'b11 ;
  assign NOT_checkForException_dInst_BITS_139_TO_137_02_ETC___d678 =
	     NOT_checkForException_dInst_BITS_139_TO_137_02_ETC___d594 &&
	     !checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d266 &&
	     checkForException_dInst[51] &&
	     (checkForException_dInst[50:39] == 12'd3072 ||
	      checkForException_dInst[50:39] == 12'd3073 ||
	      checkForException_dInst[50:39] == 12'd3074 ||
	      checkForException_dInst[50:39] == 12'd2048 ||
	      checkForException_dInst[50:39] == 12'd2049 ||
	      checkForException_dInst[50:39] == 12'd256 ||
	      checkForException_dInst[50:39] == 12'd260 ||
	      checkForException_dInst[50:39] == 12'd261 ||
	      checkForException_dInst[50:39] == 12'd262 ||
	      checkForException_dInst[50:39] == 12'd320 ||
	      checkForException_dInst[50:39] == 12'd321 ||
	      checkForException_dInst[50:39] == 12'd322 ||
	      checkForException_dInst[50:39] == 12'd323 ||
	      checkForException_dInst[50:39] == 12'd324 ||
	      checkForException_dInst[50:39] == 12'd384 ||
	      checkForException_dInst[50:39] == 12'd2496 ||
	      checkForException_dInst[50:39] == 12'd768 ||
	      checkForException_dInst[50:39] == 12'd769 ||
	      checkForException_dInst[50:39] == 12'd770 ||
	      checkForException_dInst[50:39] == 12'd771 ||
	      checkForException_dInst[50:39] == 12'd772 ||
	      checkForException_dInst[50:39] == 12'd773 ||
	      checkForException_dInst[50:39] == 12'd774 ||
	      checkForException_dInst[50:39] == 12'd832 ||
	      checkForException_dInst[50:39] == 12'd833 ||
	      checkForException_dInst[50:39] == 12'd834 ||
	      checkForException_dInst[50:39] == 12'd835 ||
	      checkForException_dInst[50:39] == 12'd836 ||
	      checkForException_dInst[50:39] == 12'd2816 ||
	      checkForException_dInst[50:39] == 12'd2818 ||
	      checkForException_dInst[50:39] == 12'd3857 ||
	      checkForException_dInst[50:39] == 12'd3858 ||
	      checkForException_dInst[50:39] == 12'd3859 ||
	      checkForException_dInst[50:39] == 12'd3860 ||
	      checkForException_dInst[50:39] == 12'd3008 ||
	      checkForException_dInst[50:39] == 12'd1952 ||
	      checkForException_dInst[50:39] == 12'd1953 ||
	      checkForException_dInst[50:39] == 12'd1954 ||
	      checkForException_dInst[50:39] == 12'd1955 ||
	      checkForException_dInst[50:39] == 12'd1968 ||
	      checkForException_dInst[50:39] == 12'd1969 ||
	      checkForException_dInst[50:39] == 12'd1970 ||
	      checkForException_dInst[50:39] == 12'd1971) ;
  assign NOT_checkForException_dInst_BIT_51_22_68_OR_NO_ETC___d417 =
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3072 ||
	      (checkForException_dInst[139:137] != 3'd0 ||
	       checkForException_dInst[114:110] != 5'd15) &&
	      rs1__h1511 == 5'd0 &&
	      imm__h1512 == 32'd0) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3074 ||
	      (checkForException_dInst[139:137] != 3'd0 ||
	       checkForException_dInst[114:110] != 5'd15) &&
	      rs1__h1511 == 5'd0 &&
	      imm__h1512 == 32'd0) ;
  assign NOT_checkForException_pcc_BIT_122_8_9_AND_NOT__ETC___d468 =
	     !checkForException_pcc[122] &&
	     NOT_checkForException_dInst_BIT_51_22_68_OR_NO_ETC___d417 ||
	     checkForException_csrState[10:9] == 2'd1 &&
	     checkForException_csrState[8] &&
	     CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 == 6'd17 ;
  assign b_base__h929 =
	     { checkForException_pcc[77:67],
	       ~checkForException_pcc[66],
	       checkForException_pcc[65:64] } ;
  assign b_top__h928 =
	     { checkForException_pcc[89:81],
	       ~checkForException_pcc[80:79],
	       checkForException_pcc[78] } ;
  assign carry_out__h594 =
	     (IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d18 <
	      x__h960[11:0]) ?
	       2'b01 :
	       2'b0 ;
  assign checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d266 =
	     checkForException_csrState[10:9] < csr__h1509[9:8] ;
  assign checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d493 =
	     checkForException_csrState[10:9] <
	     CASE_checkForException_dInst_BITS_37_TO_33_0_c_ETC__q2[4:3] ;
  assign checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d515 =
	     checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d493 ||
	     checkForException_dInst[37:33] != 5'd0 &&
	     checkForException_dInst[37:33] != 5'd1 &&
	     checkForException_dInst[37:33] != 5'd12 &&
	     checkForException_dInst[37:33] != 5'd13 &&
	     checkForException_dInst[37:33] != 5'd14 &&
	     checkForException_dInst[37:33] != 5'd15 &&
	     checkForException_dInst[37:33] != 5'd28 &&
	     checkForException_dInst[37:33] != 5'd29 &&
	     checkForException_dInst[37:33] != 5'd30 &&
	     checkForException_dInst[37:33] != 5'd31 ||
	     !checkForException_pcc[122] &&
	     checkForException_dInst[37:33] != 5'd1 ;
  assign checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d264 =
	     (checkForException_dInst[139:137] == 3'd0 &&
	      checkForException_dInst[114:110] == 5'd15 ||
	      rs1__h1511 != 5'd0 ||
	      imm__h1512 != 32'd0) &&
	     csr__h1509[11:10] == 2'b11 ;
  assign checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d406 =
	     checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d264 ||
	     checkForException_csrState_BITS_10_TO_9_5_ULT__ETC___d266 ||
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3072) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3073) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3074) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2048) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2049) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd256) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd260) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd261) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd262) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd320) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd321) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd322) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd323) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd324) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd384) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2496) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd768) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd769) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd770) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd771) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd772) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd773) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd774) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd832) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd833) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd834) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd835) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd836) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2816) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd2818) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3857) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3858) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3859) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3860) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd3008) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1952) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1953) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1954) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1955) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1968) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1969) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1970) &&
	     (!checkForException_dInst[51] ||
	      checkForException_dInst[50:39] != 12'd1971) ;
  assign cr_addrBits__h111 =
	     INV_checkForException_pcc_BITS_108_TO_90__q1[0] ?
	       x__h443[13:0] :
	       checkForException_pcc[13:0] ;
  assign cr_addrBits__h561 =
	     INV_checkForException_pcc_BITS_108_TO_90__q1[0] ?
	       x__h997[13:0] :
	       memCap_address__h637[13:0] ;
  assign csr__h1509 =
	     (checkForException_dInst[51] &&
	      checkForException_dInst[50:39] == 12'd1) ?
	       12'd1 :
	       ((checkForException_dInst[51] &&
		 checkForException_dInst[50:39] == 12'd2) ?
		  12'd2 :
		  ((checkForException_dInst[51] &&
		    checkForException_dInst[50:39] == 12'd3) ?
		     12'd3 :
		     ((checkForException_dInst[51] &&
		       checkForException_dInst[50:39] == 12'd3072) ?
			12'd3072 :
			((checkForException_dInst[51] &&
			  checkForException_dInst[50:39] == 12'd3073) ?
			   12'd3073 :
			   ((checkForException_dInst[51] &&
			     checkForException_dInst[50:39] == 12'd3074) ?
			      12'd3074 :
			      ((checkForException_dInst[51] &&
				checkForException_dInst[50:39] == 12'd2048) ?
				 12'd2048 :
				 ((checkForException_dInst[51] &&
				   checkForException_dInst[50:39] ==
				   12'd2049) ?
				    12'd2049 :
				    ((checkForException_dInst[51] &&
				      checkForException_dInst[50:39] ==
				      12'd256) ?
				       12'd256 :
				       ((checkForException_dInst[51] &&
					 checkForException_dInst[50:39] ==
					 12'd260) ?
					  12'd260 :
					  ((checkForException_dInst[51] &&
					    checkForException_dInst[50:39] ==
					    12'd261) ?
					     12'd261 :
					     ((checkForException_dInst[51] &&
					       checkForException_dInst[50:39] ==
					       12'd262) ?
						12'd262 :
						((checkForException_dInst[51] &&
						  checkForException_dInst[50:39] ==
						  12'd320) ?
						   12'd320 :
						   ((checkForException_dInst[51] &&
						     checkForException_dInst[50:39] ==
						     12'd321) ?
						      12'd321 :
						      ((checkForException_dInst[51] &&
							checkForException_dInst[50:39] ==
							12'd322) ?
							 12'd322 :
							 ((checkForException_dInst[51] &&
							   checkForException_dInst[50:39] ==
							   12'd323) ?
							    12'd323 :
							    ((checkForException_dInst[51] &&
							      checkForException_dInst[50:39] ==
							      12'd324) ?
							       12'd324 :
							       ((checkForException_dInst[51] &&
								 checkForException_dInst[50:39] ==
								 12'd384) ?
								  12'd384 :
								  ((checkForException_dInst[51] &&
								    checkForException_dInst[50:39] ==
								    12'd2496) ?
								     12'd2496 :
								     ((checkForException_dInst[51] &&
								       checkForException_dInst[50:39] ==
								       12'd768) ?
									12'd768 :
									((checkForException_dInst[51] &&
									  checkForException_dInst[50:39] ==
									  12'd769) ?
									   12'd769 :
									   ((checkForException_dInst[51] &&
									     checkForException_dInst[50:39] ==
									     12'd770) ?
									      12'd770 :
									      ((checkForException_dInst[51] &&
										checkForException_dInst[50:39] ==
										12'd771) ?
										 12'd771 :
										 ((checkForException_dInst[51] &&
										   checkForException_dInst[50:39] ==
										   12'd772) ?
										    12'd772 :
										    ((checkForException_dInst[51] &&
										      checkForException_dInst[50:39] ==
										      12'd773) ?
										       12'd773 :
										       ((checkForException_dInst[51] &&
											 checkForException_dInst[50:39] ==
											 12'd774) ?
											  12'd774 :
											  ((checkForException_dInst[51] &&
											    checkForException_dInst[50:39] ==
											    12'd832) ?
											     12'd832 :
											     ((checkForException_dInst[51] &&
											       checkForException_dInst[50:39] ==
											       12'd833) ?
												12'd833 :
												((checkForException_dInst[51] &&
												  checkForException_dInst[50:39] ==
												  12'd834) ?
												   12'd834 :
												   ((checkForException_dInst[51] &&
												     checkForException_dInst[50:39] ==
												     12'd835) ?
												      12'd835 :
												      ((checkForException_dInst[51] &&
													checkForException_dInst[50:39] ==
													12'd836) ?
													 12'd836 :
													 ((checkForException_dInst[51] &&
													   checkForException_dInst[50:39] ==
													   12'd2816) ?
													    12'd2816 :
													    ((checkForException_dInst[51] &&
													      checkForException_dInst[50:39] ==
													      12'd2818) ?
													       12'd2818 :
													       ((checkForException_dInst[51] &&
														 checkForException_dInst[50:39] ==
														 12'd3857) ?
														  12'd3857 :
														  ((checkForException_dInst[51] &&
														    checkForException_dInst[50:39] ==
														    12'd3858) ?
														     12'd3858 :
														     ((checkForException_dInst[51] &&
														       checkForException_dInst[50:39] ==
														       12'd3859) ?
															12'd3859 :
															((checkForException_dInst[51] &&
															  checkForException_dInst[50:39] ==
															  12'd3860) ?
															   12'd3860 :
															   ((checkForException_dInst[51] &&
															     checkForException_dInst[50:39] ==
															     12'd3008) ?
															      12'd3008 :
															      ((checkForException_dInst[51] &&
																checkForException_dInst[50:39] ==
																12'd1952) ?
																 12'd1952 :
																 ((checkForException_dInst[51] &&
																   checkForException_dInst[50:39] ==
																   12'd1953) ?
																    12'd1953 :
																    ((checkForException_dInst[51] &&
																      checkForException_dInst[50:39] ==
																      12'd1954) ?
																       12'd1954 :
																       ((checkForException_dInst[51] &&
																	 checkForException_dInst[50:39] ==
																	 12'd1955) ?
																	  12'd1955 :
																	  ((checkForException_dInst[51] &&
																	    checkForException_dInst[50:39] ==
																	    12'd1968) ?
																	     12'd1968 :
																	     ((checkForException_dInst[51] &&
																	       checkForException_dInst[50:39] ==
																	       12'd1969) ?
																		12'd1969 :
																		((checkForException_dInst[51] &&
																		  checkForException_dInst[50:39] ==
																		  12'd1970) ?
																		   12'd1970 :
																		   ((checkForException_dInst[51] &&
																		     checkForException_dInst[50:39] ==
																		     12'd1971) ?
																		      12'd1971 :
																		      12'd2303))))))))))))))))))))))))))))))))))))))))))))) ;
  assign imm__h1512 =
	     checkForException_dInst[32] ?
	       checkForException_dInst[31:0] :
	       32'd0 ;
  assign impliedTopBits__h596 = x__h617 + len_correction__h595 ;
  assign inc__h652 = checkForException_fourByteInst ? 12'd4 : 12'd2 ;
  assign len_correction__h595 =
	     INV_checkForException_pcc_BITS_108_TO_90__q1[0] ? 2'b01 : 2'b0 ;
  assign memCap_address__h637 =
	     checkForException_pcc[63:0] +
	     { {52{inc__h652[11]}}, inc__h652 } ;
  assign repBound__h535 = x__h960[13:11] - 3'b001 ;
  assign rs1__h1511 =
	     (checkForException_regs[19] && !checkForException_regs[18]) ?
	       checkForException_regs[17:13] :
	       5'd0 ;
  assign tb__h532 =
	     { impliedTopBits__h596,
	       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d18[11] } ;
  assign tmp_expBotHalf__h991 =
	     { ~checkForException_pcc[66], checkForException_pcc[65:64] } ;
  assign tmp_expTopHalf__h989 =
	     { ~checkForException_pcc[80:79], checkForException_pcc[78] } ;
  assign x__h1035 = { tmp_expTopHalf__h989, tmp_expBotHalf__h991 } ;
  assign x__h443 = checkForException_pcc[63:0] >> x__h1035 ;
  assign x__h617 = x__h960[13:12] + carry_out__h594 ;
  assign x__h960 =
	     INV_checkForException_pcc_BITS_108_TO_90__q1[0] ?
	       { checkForException_pcc[77:67], 3'd0 } :
	       b_base__h929 ;
  assign x__h997 = memCap_address__h637 >> x__h1035 ;
  assign y__h1054 =
	     { impliedTopBits__h596,
	       IF_INV_checkForException_pcc_BITS_108_TO_90_BI_ETC___d18 } ;
  always@(checkForException_dInst)
  begin
    case (checkForException_dInst[37:33])
      5'd0, 5'd1, 5'd12, 5'd13, 5'd14, 5'd15, 5'd28, 5'd29, 5'd30, 5'd31:
	  CASE_checkForException_dInst_BITS_37_TO_33_0_c_ETC__q2 =
	      checkForException_dInst[37:33];
      default: CASE_checkForException_dInst_BITS_37_TO_33_0_c_ETC__q2 = 5'd10;
    endcase
  end
  always@(checkForException_csrState)
  begin
    case (checkForException_csrState[14:12])
      3'd0, 3'd1, 3'd2, 3'd3, 3'd4:
	  CASE_checkForException_csrState_BITS_14_TO_12__ETC__q3 =
	      checkForException_csrState[14:12];
      default: CASE_checkForException_csrState_BITS_14_TO_12__ETC__q3 = 3'd5;
    endcase
  end
  always@(checkForException_dInst)
  begin
    case (checkForException_dInst[50:39])
      12'd1: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd0;
      12'd2: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd1;
      12'd3: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd2;
      12'd256: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd8;
      12'd260: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd9;
      12'd261: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd10;
      12'd262: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd11;
      12'd320: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd12;
      12'd321: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd13;
      12'd322: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd14;
      12'd323: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd15;
      12'd324: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd16;
      12'd384: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd17;
      12'd768: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd19;
      12'd769: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd20;
      12'd770: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd21;
      12'd771: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd22;
      12'd772: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd23;
      12'd773: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd24;
      12'd774: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd25;
      12'd832: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd26;
      12'd833: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd27;
      12'd834: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd28;
      12'd835: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd29;
      12'd836: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd30;
      12'd1952:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd38;
      12'd1953:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd39;
      12'd1954:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd40;
      12'd1955:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd41;
      12'd1968:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd42;
      12'd1969:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd43;
      12'd1970:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd44;
      12'd1971:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd45;
      12'd2048: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd6;
      12'd2049: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd7;
      12'd2496:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd18;
      12'd2816:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd31;
      12'd2818:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd32;
      12'd3008:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd37;
      12'd3072: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd3;
      12'd3073: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd4;
      12'd3074: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd5;
      12'd3857:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd33;
      12'd3858:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd34;
      12'd3859:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd35;
      12'd3860:
	  CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd36;
      default: CASE_checkForException_dInst_BITS_50_TO_39_1_0_ETC__q4 = 6'd46;
    endcase
  end
  always@(checkForException_dInst or
	  IF_checkForException_dInst_BIT_38_70_THEN_chec_ETC___d562 or
	  checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d406 or
	  NOT_checkForException_pcc_BIT_122_8_9_AND_NOT__ETC___d468 or
	  checkForException_csrState or checkForException_pcc)
  begin
    case (checkForException_dInst[144:140])
      5'd17:
	  IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566 =
	      checkForException_dInst_BITS_139_TO_137_02_EQ__ETC___d406 ||
	      NOT_checkForException_pcc_BIT_122_8_9_AND_NOT__ETC___d468;
      5'd21:
	  IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566 =
	      checkForException_csrState[10:9] == 2'd1 &&
	      checkForException_csrState[8];
      5'd24:
	  IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566 =
	      checkForException_csrState[10:9] == 2'd0 ||
	      checkForException_csrState[10:9] == 2'd1 &&
	      checkForException_csrState[6] ||
	      !checkForException_pcc[122];
      5'd25:
	  IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566 =
	      checkForException_csrState[10:9] != 2'd3 ||
	      !checkForException_pcc[122];
      default: IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d566 =
		   IF_checkForException_dInst_BIT_38_70_THEN_chec_ETC___d562;
    endcase
  end
  always@(checkForException_dInst or
	  IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d681 or
	  checkForException_csrState)
  begin
    case (checkForException_dInst[144:140])
      5'd24:
	  CASE_checkForException_dInst_BITS_144_TO_140_2_ETC__q5 =
	      checkForException_csrState[10:9] != 2'd0 &&
	      (checkForException_csrState[10:9] != 2'd1 ||
	       !checkForException_csrState[6]);
      5'd25:
	  CASE_checkForException_dInst_BITS_144_TO_140_2_ETC__q5 =
	      checkForException_csrState[10:9] == 2'd3;
      default: CASE_checkForException_dInst_BITS_144_TO_140_2_ETC__q5 =
		   checkForException_dInst[144:140] != 5'd21 &&
		   IF_checkForException_dInst_BITS_144_TO_140_1_E_ETC___d681;
    endcase
  end
endmodule  // module_checkForException

