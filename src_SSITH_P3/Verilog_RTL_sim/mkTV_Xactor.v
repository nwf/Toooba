//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
//
//
//
// Ports:
// Name                         I/O  size props
// RDY_tv_in_put                  O     1 reg
// axi_out_tvalid                 O     1 reg
// axi_out_tdata                  O   608 reg
// axi_out_tstrb                  O    76 reg
// axi_out_tkeep                  O    76 reg
// axi_out_tlast                  O     1 reg
// CLK                            I     1 clock
// RST_N                          I     1 reset
// tv_in_put                      I   608 reg
// axi_out_tready                 I     1
// EN_tv_in_put                   I     1
//
// No combinational paths from inputs to outputs
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

module mkTV_Xactor(CLK,
		   RST_N,

		   tv_in_put,
		   EN_tv_in_put,
		   RDY_tv_in_put,

		   axi_out_tvalid,

		   axi_out_tdata,

		   axi_out_tstrb,

		   axi_out_tkeep,

		   axi_out_tlast,

		   axi_out_tready);
  input  CLK;
  input  RST_N;

  // action method tv_in_put
  input  [607 : 0] tv_in_put;
  input  EN_tv_in_put;
  output RDY_tv_in_put;

  // value method axi_out_m_tvalid
  output axi_out_tvalid;

  // value method axi_out_m_tid

  // value method axi_out_m_tdata
  output [607 : 0] axi_out_tdata;

  // value method axi_out_m_tstrb
  output [75 : 0] axi_out_tstrb;

  // value method axi_out_m_tkeep
  output [75 : 0] axi_out_tkeep;

  // value method axi_out_m_tlast
  output axi_out_tlast;

  // value method axi_out_m_tdest

  // value method axi_out_m_tuser

  // action method axi_out_m_tready
  input  axi_out_tready;

  // signals for module outputs
  wire [607 : 0] axi_out_tdata;
  wire [75 : 0] axi_out_tkeep, axi_out_tstrb;
  wire RDY_tv_in_put, axi_out_tlast, axi_out_tvalid;

  // ports of submodule tv_xactor_f_data
  wire [760 : 0] tv_xactor_f_data$D_IN, tv_xactor_f_data$D_OUT;
  wire tv_xactor_f_data$CLR,
       tv_xactor_f_data$DEQ,
       tv_xactor_f_data$EMPTY_N,
       tv_xactor_f_data$ENQ,
       tv_xactor_f_data$FULL_N;

  // rule scheduling signals
  wire CAN_FIRE_axi_out_m_tready,
       CAN_FIRE_tv_in_put,
       WILL_FIRE_axi_out_m_tready,
       WILL_FIRE_tv_in_put;

  // action method tv_in_put
  assign RDY_tv_in_put = tv_xactor_f_data$FULL_N ;
  assign CAN_FIRE_tv_in_put = tv_xactor_f_data$FULL_N ;
  assign WILL_FIRE_tv_in_put = EN_tv_in_put ;

  // value method axi_out_m_tvalid
  assign axi_out_tvalid = tv_xactor_f_data$EMPTY_N ;

  // value method axi_out_m_tdata
  assign axi_out_tdata = tv_xactor_f_data$D_OUT[760:153] ;

  // value method axi_out_m_tstrb
  assign axi_out_tstrb = tv_xactor_f_data$D_OUT[152:77] ;

  // value method axi_out_m_tkeep
  assign axi_out_tkeep = tv_xactor_f_data$D_OUT[76:1] ;

  // value method axi_out_m_tlast
  assign axi_out_tlast = tv_xactor_f_data$D_OUT[0] ;

  // action method axi_out_m_tready
  assign CAN_FIRE_axi_out_m_tready = 1'd1 ;
  assign WILL_FIRE_axi_out_m_tready = 1'd1 ;

  // submodule tv_xactor_f_data
  FIFO2 #(.width(32'd761), .guarded(32'd1)) tv_xactor_f_data(.RST(RST_N),
							     .CLK(CLK),
							     .D_IN(tv_xactor_f_data$D_IN),
							     .ENQ(tv_xactor_f_data$ENQ),
							     .DEQ(tv_xactor_f_data$DEQ),
							     .CLR(tv_xactor_f_data$CLR),
							     .D_OUT(tv_xactor_f_data$D_OUT),
							     .FULL_N(tv_xactor_f_data$FULL_N),
							     .EMPTY_N(tv_xactor_f_data$EMPTY_N));

  // submodule tv_xactor_f_data
  assign tv_xactor_f_data$D_IN =
	     { tv_in_put, 153'h1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF } ;
  assign tv_xactor_f_data$ENQ = EN_tv_in_put ;
  assign tv_xactor_f_data$DEQ = tv_xactor_f_data$EMPTY_N && axi_out_tready ;
  assign tv_xactor_f_data$CLR = 1'b0 ;
endmodule  // mkTV_Xactor

