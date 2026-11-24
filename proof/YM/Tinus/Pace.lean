import YM.Tinus.Julep
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open RG YM.Massive.Poised.Stative Lattice Wilson QCD UV Finset Function Filter
open scoped BigOperators Topology Classical
-- unroll EnergyD actual data.M.Tr takes S_n large growthProof.Arch.Mark.End.jX=q case.N.Key
variable {u:ℝ}(P:ℕ→BudgetPoint)(K v a:ℕ→ℝ)(L a' η εK εA C X δ:ℝ)(x:ℕ→Label 8)(w s:ℕ→ℝ)(n:ℕ)
-- v:waveW. K scale
local notation "Y" i:arg=> ((K i):ℂ) • x i
local notation "S" i:arg=> K i*s i/(w i)^2
local notation "PY" i:arg=> laps 6 ((K i:ℂ) • x i) +laps 8 ((K i:ℂ) • x i)
local notation "Ω" => (Fintype.card (Rings 8):ℝ)*4*L
structure Voyage (u:ℝ) (B Γ:ℝ) :Prop where
      bounce(i:ℕ)(ht:i<n) : K i=K (i+1)*L
      speed(i:ℕ)(h:i≤ n): 0 < K i
      trusts : K n=1
      back: L*u^8=1
      away: 0<u
      dawn: u≤1
      lens : 0≤ a'
      band (i:ℕ)(h:i≤n) :0 < w i
      gear (i:ℕ)(h:i<n) : w (i+1) ≤2*w i
      reflects (i:ℕ)(h:i<n) : |(v i)^2-1| ≤ η
      forth (i:ℕ)(h:i<n): 2 ≤ L*(u^6*(v i)^2)
      grant : 4*a'*u ≤ 1/2
      tonic : 0≤ εK
      fee : 0≤ η
      past : 0≤ B
      rents : S n ≤ B
      glories(i:ℕ)(h:i≤ n) : OffS (x i)
      erupts(i:ℕ)(h:i<n) : s i ≤ a'*(toted u (x (i+1)) (P (i+1)) (w (i+1))+u^9*s (i+1)) + wealth (x i).val (P i).threshold (w i)
      learns(i:ℕ)(h:i≤ n): wealth (x i).val (P i).threshold (w i) ≤ s i
      careful(i:ℕ)(h:i<n) : TypeBeta u (w (i+1)) (w i) (v i * w i) Γ εK (εK*s (i+1)) (P (i+1)) (P i) (x (i+1)) (x i)
      positive : 0 ≤ L ∧ 0 ≤ Γ -- redundant first
#check Voyage
local notation "Wz"=> fun i=> ((K i):ℂ) • x i
local notation "Sz"=> fun i=> K i*s i/(w i)^2
variable {T Z:ℝ}(h:Voyage P K v L a' η εK x w s n u T Z)
include h
set_option maxHeartbeats 850000 in
lemma axes (ht: laps 6 ((Wz) 0) ≤ X): Premium Wz Sz n (4*L*a') (Ω*Z*u^6) X T (Ω*2*εK) η:=by
      have heP :0<L:=by have hh:0 ≤ L:= h.positive.1; by_contra! hx; have hQ:= h.back; rw [eq_of_le_of_not_lt hx (not_lt_of_ge hh),zero_mul] at hQ; norm_num at hQ
      have hu:=h.away; have hg:=h.lens; have hp:=h.positive.2; have hε:=h.tonic
      refine ⟨by positivity,by positivity, ht,h.rents,fun i hv=>?_, h.past, by positivity,h.fee,fun i hv=>?_,fun i hv=>?_⟩
      · have hh:= sellsP (x (i+1)) (x i) h.back heP (h.speed _ hv) h.away h.dawn h.lens h.grant ((wealth_ge ..).trans (h.learns _ hv)) (h.glories _ hv) (h.glories _ hv.le) (h.band _ hv) (h.band _ hv.le) (h.gear _ hv) (h.erupts _ hv) (show K (i+1)*s (i+1)/(w (i+1))^2=_ from rfl); rw [h.bounce i hv]; exact hh
      · have hh:=realFu (x (i+1)) (x i) h.back 6 (.inl rfl) _ rfl hu (h.speed _ hv) (h.careful _ hv) heP hp hε (h.band _ hv) (h.band _ hv.le) (h.gear _ hv) (h.learns _ hv) (show K (i+1)*s (i+1)/(w (i+1))^2=_ from rfl) (h.glories _ hv) (h.glories _ hv.le); rw [←h.bounce i hv,if_neg (by decide), zero_add] at hh
        exact (winds (Y (i+1)) (Y i) (h.forth i hv) hh).trans_eq (by ring)
      have hx: L*(u^8*(v i)^2)=(v i)^2:=by rw[←mul_assoc,h.back,one_mul]
      have hh:= realFu (x (i+1)) (x i) h.back 8 (.inr rfl) _ hx hu (h.speed _ hv) (h.careful _ hv) heP hp hε (h.band _ hv) (h.band _ hv.le) (h.gear _ hv) (h.learns _ hv) (show K (i+1)*s (i+1)/(w (i+1))^2=_ from rfl) (h.glories _ hv) (h.glories _ hv.le); rw [←h.bounce i hv,if_pos rfl] at hh
      exact (cashY _ _ _ hh (h.reflects i hv)).trans_eq (by ring)
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.axes
