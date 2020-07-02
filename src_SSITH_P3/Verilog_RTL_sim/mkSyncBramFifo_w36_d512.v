//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Thu Jul  2 02:54:40 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// RDY_enq                        O     1
// RDY_deq                        O     1
// first                          O    36
// RDY_first                      O     1
// notFull                        O     1
// RDY_notFull                    O     1 const
// notEmpty                       O     1
// RDY_notEmpty                   O     1 const
// CLK_srcClk                     I     1 clock
// RST_N_srcRst                   I     1 reset
// CLK_dstClk                     I     1 clock
// enq_sendData                   I    36
// EN_enq                         I     1
// EN_deq                         I     1
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

module mkSyncBramFifo_w36_d512(CLK_srcClk,
			       RST_N_srcRst,
			       CLK_dstClk,

			       enq_sendData,
			       EN_enq,
			       RDY_enq,

			       EN_deq,
			       RDY_deq,

			       first,
			       RDY_first,

			       notFull,
			       RDY_notFull,

			       notEmpty,
			       RDY_notEmpty);
  input  CLK_srcClk;
  input  RST_N_srcRst;
  input  CLK_dstClk;

  // action method enq
  input  [35 : 0] enq_sendData;
  input  EN_enq;
  output RDY_enq;

  // action method deq
  input  EN_deq;
  output RDY_deq;

  // value method first
  output [35 : 0] first;
  output RDY_first;

  // value method notFull
  output notFull;
  output RDY_notFull;

  // value method notEmpty
  output notEmpty;
  output RDY_notEmpty;

  // signals for module outputs
  wire [35 : 0] first;
  wire RDY_deq,
       RDY_enq,
       RDY_first,
       RDY_notEmpty,
       RDY_notFull,
       notEmpty,
       notFull;

  // ports of submodule q
  wire [35 : 0] q$dD_OUT, q$sD_IN;
  wire q$dDEQ, q$dEMPTY_N, q$sENQ, q$sFULL_N;

  // rule scheduling signals
  wire CAN_FIRE_deq, CAN_FIRE_enq, WILL_FIRE_deq, WILL_FIRE_enq;

  // action method enq
  assign RDY_enq = q$sFULL_N ;
  assign CAN_FIRE_enq = q$sFULL_N ;
  assign WILL_FIRE_enq = EN_enq ;

  // action method deq
  assign RDY_deq = q$dEMPTY_N ;
  assign CAN_FIRE_deq = q$dEMPTY_N ;
  assign WILL_FIRE_deq = EN_deq ;

  // value method first
  assign first = q$dD_OUT ;
  assign RDY_first = q$dEMPTY_N ;

  // value method notFull
  assign notFull = q$sFULL_N ;
  assign RDY_notFull = 1'd1 ;

  // value method notEmpty
  assign notEmpty = q$dEMPTY_N ;
  assign RDY_notEmpty = 1'd1 ;

  // submodule q
  SyncFIFO #(.dataWidth(32'd36),
	     .depth(32'd512),
	     .indxWidth(32'd9)) q(.sCLK(CLK_srcClk),
				  .dCLK(CLK_dstClk),
				  .sRST(RST_N_srcRst),
				  .sD_IN(q$sD_IN),
				  .sENQ(q$sENQ),
				  .dDEQ(q$dDEQ),
				  .sFULL_N(q$sFULL_N),
				  .dEMPTY_N(q$dEMPTY_N),
				  .dD_OUT(q$dD_OUT));

  // submodule q
  assign q$sD_IN = enq_sendData ;
  assign q$sENQ = EN_enq ;
  assign q$dDEQ = EN_deq ;
endmodule  // mkSyncBramFifo_w36_d512

