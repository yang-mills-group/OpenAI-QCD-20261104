import YM.Clink.Reams
import YM.Clink.Rice
/-! Path data and mask room. Pack job layout. Cost normalized at post.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J D E :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Basal.Surge
open QCD.Ruby Cove NormedSpace
open Massive.PCAC Massive.PCAC.Oren
variable {c f' L:Side}{v t x δ α β κ ρ C C' ξ M B3 G3 σ B1 G1 a D_:ℝ}{P:BudgetPoint}{k n l m N:ℕ}
variable (o:I → Cover)(W S:St c)(p:Set (Finset I))(F:Flavor 6)(X:Axis)(W':St c)
local notation "R'"=> Flavor 6
-- explicit suffix list build avoids type instances. polynomial budgets preL with fixed L Card. θ at q.Set.
variable (f g:R'→ℂ)
noncomputable def SunAt (X:Axis) (S:St c) (f g:Flavor 6→ℂ)(F:Flavor 6):List (Flavor 6)→ Surge c
   | []=>Surge.tilde F S X
   | b::l=> SunAt X S f g F l + (f b • Surge.solo b c X+g b • Surge.hark b c X)
open WindowU
local notation "h!"=> hark
local notation "b₂"=> (25/256:ℝ)
local notation "μ"=> (1/512:ℝ)
local notation "ε"=> (1/256:ℝ)
local notation "UP"=> wrap c∘o
local notation "κG"=> (Fintype.card I:ℝ)
local notation "F'!"=> mCash P.B P.power P.order k μ b₂
local notation "NQ"=>anth ε (b₂+2*ε) P.B
local notation "U'"=> (P.threshold)
open Rails.Tantra
variable (ht:1 ≤ v)(hz: 0 ≤ ξ)(hP:∀ i∈ p,i.card≤1)(h0: 1< P.B*P.B)
include ht hz hP h0
variable (hK:ColorDuty W a v P)(hS:W=S+W')(T:ℝ)(hr: BudgetB P.order P.power M)(h:∀ i:I,WindowU.Given (wrap c (o i)) P v (25/256) (T*v^2 *P.threshold) (T*v^2) (Entr.Meridian.aurasigmaMont F ((wrap c ∘ o) i) X S+Entr.Meridian.sourceT F ((wrap c ∘ o) i) X W'))(he:0 ≤ T)
-- hr needs `∀ order` given ∃ for ξ's n.D.
local notation "fB"=> κG*(ξ*(T*v^2 *P.threshold))
local notation "fU"=> κG*(ξ*(T*v^2))
variable (l':ℝ)
local notation "kL"=>(l'*ξ)
local notation "BK"=>mCash P.B P.power P.order k μ b₂ (M*(l'*ξ))*(Basal.anth ε (b₂+2*ε) P.B*(a*v^2))
local notation "BZ"=> κG*((l'*ξ)* cashZ v b₂)
local notation "k'"=> BK + BZ
variable (Lq: List (Flavor 6))(hW:Fires (wrap c∘o) k)(hg:∀ i∈p,Spaced (wrap c ∘ o) i P.B)
include hK hS hr h he hW hg
lemma fame (hk:0 ≤ l')(hm:l' ≤1)(hf:‖f‖≤ l')(hs:‖g‖≤ l')(hΩ:hullP P.B k*(Real.exp (b₂+μ)*(M*(l'*ξ)*2^P.order))≤μ): Owns (SunAt X S f g F Lq) o P W p b₂ v (M+Lq.length*(M+M)) ξ (fB+(Lq.length:ℝ)*(k')) (fU+(Lq.length:ℝ)*(k')):=by
       have hl:0 ≤ kL:=mul_nonneg hk hz; have hu:l'*M≤ M:=mul_le_of_le_one_left hr.nng hm
       have hT:= κp (ξ:=ξ) o W S p F X W' hP ht (fun i=>(hr.b P le_rfl le_rfl c _ X F).2.2) hS h he -- signature
       let P1(b:R'):= f b • Surge.solo b c X + g b • Surge.hark b c X; have ht1 (b): Owns (P1 b) o P W p b₂ v (M+M) ξ k' k' :=by
             have hh:Owns (Surge.solo b c X) o P W p b₂ v M kL BK BK:= owns0 o W p (Surge.solo b c X) ht k hK hl hr.nng hW h0 hg rfl (fun i=> (hr.b P le_rfl le_rfl c _ X b).1) hΩ
             let Z:= Surge.hark b c X; have hp : Owns Z o P W p b₂ v M kL BZ BZ:= δZ o W p b X hP ht hr.nng
             have he:= joins (f b • Surge.solo b c X) (g b • Z) o W p (resizeA _ o W p hh (f b) l' M ((norm_le_pi_norm ..).trans hf) hu hz le_rfl hr.nng hP) (by norm_num) ht hP (resizeA Z _ _ _ hp _ _ _ ((norm_le_pi_norm ..).trans hs) hu hz le_rfl hr.nng hP); exact he
       induction Lq with
       | nil=> simp only[List.length_nil,SunAt,Nat.cast_zero,zero_mul,add_zero]; exact hT
       | cons b l ih=>
          dsimp only[List.length_cons, SunAt]; push_cast; convert joins _ _ _ W p ih (show 0 ≤ b₂ from by norm_num) ht hP (ht1 b) using 1<;> first| rfl| ring
-- eats formula at every b
omit ht hz hP h0 hK hS hr h he hW hg
variable {d₁:ℕ} {S':Massive.Scheme} {R:Side}(A:Massive.Run S' N R 6)(i:ℕ)(B:Plan d₁)(H:Train d₁)(m1:ℝ)
local notation "V!"=> A.density i
local notation "P!"=> cedar d₁ B H m1 (S'.side R i)
lemma owns_R (b:Cover)(U:Grid (S'.side R i)): eats (SunAt X (cedar d₁ B H m1 (S'.side R i)) f g F (univ:Finset (Flavor 6)).toList) (⇑(actor A i)) b U=lobbyR (i:=i) A d₁ B H m1 F f g X b U :=by
       let K:= corm (i:=i) A d₁ B H m1 F X; let V(z:Flavor 6):= bead (i:=i) A f g z; let R(L:List (Flavor 6)):=SunAt X (cedar d₁ B H m1 (S'.side R i)) f g F L; let y:=actor A i; have hh (L:List (Flavor 6)) (h:L.Nodup): eats (R L) y b U = K b U + ∑ i∈L.toFinset, V i X b U:=by
           induction L with
           | nil=> rw[List.toFinset_nil,Finset.sum_empty,add_zero]; exact (congr_fun (gets0 ..) U).symm
           | cons a l ih=>
               unfold R SunAt; rw [sumE]; simp_rw [sumE, buyE]; rw [Pi.add_apply,Pi.add_apply, Pi.smul_apply,Pi.smul_apply, show eats _ _ _ U= _ from ih (List.Nodup.tail h),←congr_fun (gets1 ..) U,←congr_fun (getsZ ..) U,List.toFinset_cons,sum_insert]; swap; · simpa using h.notMem
               rw [add_assoc,add_comm (∑ i∈l.toFinset,V i X b U)]; rfl
       rw [hh _ (nodup_toList _)]; rw [toList_toFinset]; unfold lobbyR; simp_rw [Pi.add_apply,Finset.sum_apply,ContinuousMap.add_apply,ContinuousMap.sum_apply]; rfl
end Basal.Surge
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.Surge.fame
#print axioms YM.MassiveQCD.Sample.Basal.Surge.owns_R
