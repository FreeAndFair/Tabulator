------------------------------------------------------------------------------
-- (C) Free & Fair
------------------------------------------------------------------------------
--
-- The Free & Fair Tabulator is free software.
--
-- redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
-- * Redistributions of source code must retain the above copyright notice, this
--   list of conditions and the following disclaimer.
--
-- * Redistributions in binary form must reproduce the above copyright notice,
--   this list of conditions and the following disclaimer in the documentation
--   and/or other materials provided with the distribution.
--
-- * Neither the names of the copyright holders nor the names of its
--   contributors may be used to endorse or promote products derived from
--   this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--==============================================================================

package Tabulation_Computation
 -- Computational concepts associated with tabulation.  Typically sets
 -- of ballots are tabulated to determine winning candidates or an answer
 -- to a ballot question."
is
  -- A function that tabulates according to a specific election method.
  type Tabulation_Algorithm;
  -- Tabulation of the plurality voting method.
  type Plurality_Tabulation_Algorithm;
  -- A tabulator for an RCV voting methods.
  type Rcv_Tabulation_Algorithm;
  -- A tabulator for San Francisco County and City's version of an RCV method.
  type San_Francisco_Rcv_Tabulation_Algorithm;
  -- A tabulator for an approval voting method.
  type Approval_Tabulation_Algorithm;
end Tabulation_Computation;
