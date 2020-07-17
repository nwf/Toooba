
// Copyright (c) 2017 Massachusetts Institute of Technology
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

`include "ProcConfig.bsv"
import Types::*;
import ProcTypes::*;
import Vector::*;
import ConfigReg::*;
import HasSpecBits::*;
import Ehr::*;
import GetPut::*;
import Assert::*;
import FIFOF::*;
import ConfigReg::*;

typedef struct{
    a data;
    PhyRegs regs;
    InstTag tag;
    // speculation
    SpecBits spec_bits;
    Maybe#(SpecTag) spec_tag;
    // scheduling
    RegsReady regs_ready;
} ToReservationStation#(type a) deriving(Bits, Eq, FShow);

interface ReservationStation#(
    numeric type size, numeric type setRegReadyNum, type a
);
    method Action enq(ToReservationStation#(a) x);
    method Bool canEnq;

    method Action setRobEnqTime(InstTime t);
    method ToReservationStation#(a) dispatchData;
    method Action doDispatch;

    interface Vector#(setRegReadyNum, Put#(Maybe#(PhyRIndx))) setRegReady;

    // For count-based scheduling when there are multiple reservation stations
    // for the same inst type. This method only takes effect when module
    // parameter countValid is true.
    method Bit#(TLog#(TAdd#(size, 1))) approximateCount;

    // performance: count full cycles
    method Bool isFull_ehrPort0;

    interface SpeculationUpdate specUpdate;
endinterface

typedef Bit#(TAdd#(1, TLog#(NumInstTags))) VirtualInstTime;

module mkReservationStation#(Bool lazySched, Bool lazyEnq, Bool countValid)(
    ReservationStation#(size, setRegReadyNum, a)
) provisos (
    NumAlias#(regsReadyPortNum, TAdd#(1, setRegReadyNum)),
    Alias#(idxT, Bit#(TLog#(size))),
    Alias#(countT, Bit#(TLog#(TAdd#(size, 1)))),
    Log#(TAdd#(1, size), TLog#(TAdd#(size, 1))),
    Bits#(a, aSz), FShow#(a),
    Add#(1, b__, size)
);

   Bool verbose = False;

    Integer valid_wrongSpec_port = 1;
    Integer valid_dispatch_port = 1; // write valid
    Integer valid_enq_port = 2; // write valid

    Integer sb_wrongSpec_port = 1;
    Integer sb_dispatch_port = 1;
    Integer sb_enq_port = 1; // write spec_bits
    Integer sb_correctSpec_port = 2; // write spec_bits

    function Integer ready_set_port(Integer i) = i; // write regs_ready by each setRegReady ifc
    Integer ready_enq_port = valueof(setRegReadyNum); // write regs_ready

    Ehr#(3,Vector#(size, Bool))                      valid      <- mkEhr(replicate(False));
    Vector#(size, Reg#(a))                           data       <- replicateM(mkConfigRegU);
    Vector#(size, Reg#(PhyRegs))                     regs       <- replicateM(mkConfigRegU);
    Vector#(size, Reg#(InstTag))                     tag        <- replicateM(mkConfigRegU);
    Vector#(size, Reg#(Maybe#(SpecTag)))             spec_tag   <- replicateM(mkConfigRegU);
    Ehr#(3, Vector#(size, SpecBits))                 spec_bits  <- mkEhr(?);
    Ehr#(regsReadyPortNum, Vector#(size, RegsReady)) regs_ready <- mkEhr(?);

    FIFOF#(SpecBits)                     correctSpecF <- mkUGFIFOF;
    FIFOF#(IncorrectSpeculation)       incorrectSpecF <- mkUGFIFOF;

    // approximate count of valid entries
    Reg#(countT) validEntryCount <- mkConfigReg(0);

    if(countValid) begin
        (* fire_when_enabled, no_implicit_conditions *)
        rule countValidEntries;
            validEntryCount <= pack(countElem(True, valid[1]));
        endrule
    end

    (* fire_when_enabled, no_implicit_conditions *)
    rule canon_speculation;
        Vector#(size, SpecBits) newSpecBits = spec_bits[0];
        Vector#(size, Bool) newValid = valid[0];
        // Fold in CorrectSpec update:
        if (correctSpecF.notEmpty) begin
            SpecBits mask = correctSpecF.first();
            correctSpecF.deq();
            // clear spec bits for all entries
            for (Integer i=0; i<valueOf(size); i=i+1)
                newSpecBits[i] = newSpecBits[i] & mask;
        end
        // Fold in IncorrectSpec update:
        if (incorrectSpecF.notEmpty) begin
            IncorrectSpeculation incSpec = incorrectSpecF.first();
            incorrectSpecF.deq();
            // clear entries
            for (Integer i=0; i<valueOf(size); i=i+1)
                if(incSpec.killAll || newSpecBits[i][incSpec.specTag] == 1'b1)
                    newValid[i] = False;
        end
        spec_bits[0] <= newSpecBits;
        valid[0] <= newValid;
    endrule

    // enq time in ROB, used as pivot to get virtual inst time (dispatch happens before ROB enq)
    Wire#(InstTime) robEnqTime <- mkDWire(0);
    // mapping to virtual inst time as follow:
    // valid entry time t --> t < robEnqTime ? t + 2^log(NumInstTags) : t
    function VirtualInstTime getVTime(InstTag instTag);
        InstTime t = instTag.t;
        return t < robEnqTime ? zeroExtend(t) + fromInteger(valueof(TExp#(TLog#(NumInstTags)))) : zeroExtend(t);
    endfunction
    Vector#(size, VirtualInstTime) vTime = map(getVTime, readVReg(tag));
    // function to find the oldest entry (smaller virtual time) which satisfy certain constraint
    function Maybe#(idxT) findOldest(Vector#(size, Bool) pred);
        function idxT getOlder(idxT a, idxT b);
            if(!pred[a]) begin
                return b;
            end
            else if(!pred[b]) begin
                return a;
            end
            else begin
                return vTime[a] < vTime[b] ? a : b;
            end
        endfunction
        Vector#(size, idxT) idxVec = genWith(fromInteger);
        idxT idx = fold(getOlder, idxVec);
        return pred[idx] ? Valid (idx) : Invalid;
    endfunction

    // search for row to dispatch, we do it lazily
    // i.e. look at the EHR port 0 of ready bits, so there is no bypassing
    staticAssert(lazySched, "Only support lazy schedule now");

    Vector#(size, Wire#(Bool)) ready_wire <- replicateM(mkBypassWire);
    (* fire_when_enabled, no_implicit_conditions *)
    rule setReadyWire;
        function Action setReady(Integer i);
        action
            ready_wire[i] <= allRegsReady(regs_ready[0][i]);
        endaction
        endfunction
        Vector#(size, Integer) idxVec = genVector;
        joinActions(map(setReady, idxVec));
    endrule

    function Bool get_ready(Wire#(Bool) r);
        return r;
    endfunction
    Vector#(size, Bool) can_schedule = zipWith( \&& , valid[valid_dispatch_port], map(get_ready, ready_wire) );

    // oldest index to dispatch
    let can_schedule_index = findOldest(can_schedule);

    // ifc to set reg ready
    Vector#(setRegReadyNum, Put#(Maybe#(PhyRIndx))) setRegReadyIfc = ?;
    for(Integer k = 0; k < valueof(setRegReadyNum); k = k+1) begin
        setRegReadyIfc[k] = (interface Put;
            method Action put(Maybe#(PhyRIndx) x);
                Integer ehrPort = ready_set_port(k);
                Vector#(size, RegsReady) new_regs_ready = regs_ready[ehrPort];
                for(Integer i=0; i<valueOf(size); i=i+1) begin
                    // function to set ready for element i
                    // This compares Maybe types.
                    // If both are invalid, regs_ready.srcX must be True.

                    if (x == regs[i].src1) begin
                        new_regs_ready[i].src1 = True;
                    end
                    if (x == regs[i].src2) begin
                        new_regs_ready[i].src2 = True;
                    end
                    if (x == regs[i].src3) begin
                        new_regs_ready[i].src3 = True;
                    end
                end
                regs_ready[ehrPort] <= new_regs_ready;
            endmethod
        endinterface);
    end

    // search to find enq slot
    Maybe#(UInt#(TLog#(size))) enqP = ?;
    function Bool entryInvalid(Bool v) = !v;

    if(lazyEnq) begin
        Wire#(Maybe#(UInt#(TLog#(size)))) enqP_wire <- mkBypassWire;
        (* fire_when_enabled, no_implicit_conditions *)
        rule setWireForEnq;
            enqP_wire <= findIndex(entryInvalid, valid[1]);
        endrule
        enqP = enqP_wire;
    end
    else begin
        enqP = findIndex(entryInvalid, valid[valid_enq_port]);
    end

    //rule debugRes(!isValid(enqP));
    //    $fdisplay(stdout, "cannot enqueue in the reservation station this cycle");
    //endrule

    method Action enq(ToReservationStation#(a) x) if (enqP matches tagged Valid .idx);
       if (verbose)
        $display("  [mkReservationStationRow::_write] ", fshow(x));
        valid[valid_enq_port][idx] <= True;
        data[idx] <= x.data;
        regs[idx] <= x.regs;
        tag[idx] <= x.tag;
        spec_tag[idx] <= x.spec_tag;
        spec_bits[sb_enq_port][idx] <= x.spec_bits;
        regs_ready[ready_enq_port][idx] <= x.regs_ready;
    endmethod
    method Bool canEnq = isValid(enqP);

    method Action setRobEnqTime(InstTime t);
        robEnqTime <= t;
    endmethod

    method ToReservationStation#(a) dispatchData if (can_schedule_index matches tagged Valid .i);
        return ToReservationStation{
            data: data[i],
            regs: regs[i],
            tag: tag[i],
            spec_bits: spec_bits[sb_dispatch_port][i],
            spec_tag: spec_tag[i],
            regs_ready: RegsReady { // must be all true
                src1: True,
                src2: True,
                src3: True,
                dst: True
            }
        };
    endmethod

    method Action doDispatch if (can_schedule_index matches tagged Valid .i);
        valid[valid_dispatch_port][i] <= False;
    endmethod

    method countT approximateCount;
        return validEntryCount;
    endmethod

    interface setRegReady = setRegReadyIfc;

    method Bool isFull_ehrPort0;
        return valid[1] == replicate(True);
    endmethod

    interface SpeculationUpdate specUpdate;
        method correctSpeculation = correctSpecF.enq;
        method incorrectSpeculation(killAll, specTag) =
            incorrectSpecF.enq(IncorrectSpeculation{killAll: killAll, specTag: specTag});
    endinterface
endmodule
