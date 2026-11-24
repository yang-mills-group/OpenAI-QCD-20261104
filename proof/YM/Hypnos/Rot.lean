import YM.Mills.Glove
import YM.QCD.Spice.Zircon
/-!
# Opening-operators real physical normalization. Pack cost when tested with dollars independent of mask flags.
 Truncate to VERY short.Sym matrix if desired. Price uses feasibility tower. This does not replace any actual polymer weight.
-/
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.Tee
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees Pressure
open Garden Spice Jets Sun LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p ε α β t:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
namespace Rot
-- polymer.P X.H.P.F.D. eligible high.short support
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "S"=> sliceL G h
section pack
variable {D E:Type*} [Fintype D] [Fintype E]
variable {X:Land f D E}{Y:Pays f D E}{o:D→Site f} {p₀:E→Site f}{T:Grid f→ArrayL D E}
variable (H:Pack o p₀ δ u l T q X Y)
include H
lemma packet (he: 0 ≤u) (i:D)(j:E) : (0 ≤ duel Y i j u l)∧duel Y i j u l≤ q := by
    have h j : 0≤ duel Y i j u l:=Finset.sum_nonneg (fun a _=>mul_nonneg (fair ..).le (H.crop i _ _).1)
    exact ⟨h _,(Finset.single_le_sum (fun p _=>h p) (Finset.mem_univ j)).trans (H.spends i)⟩
omit H
-- explicit surgeon estimate for any matrix Crop
end pack
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)

def shortS (r l:ℕ) : Finset (Support f):= Finset.univ.filter (fun i=> ¬ broad r l (Sum.inl i))
def spore (r:ℕ)(U:Grid f):Matrix A A ℂ:= ∑ i∈shortS r l,ship P.X i (settled U)
def spider (F: ℕ)(G: Flight j k)(h:f.val=c.val*G.L.val) : Matrix (Modes f F) (Modes f F) ℂ:= copies F ((father G h)⁻¹)
def wheelsF (F : ℕ)(G:Flight j k)(h:f.val=c.val*G.L.val): Water c f F:= foamB (cell (proton G h)) (cell (barP G h))
-- row support geometry
lemma spine (U:Grid f)(i j:A)(hP:spore P r U i j≠ 0): j.1.1 ∈ trunkFt (i.1.1) r := by
    unfold spore at hP; rw [Matrix.sum_apply] at hP
    contrapose! hP; apply sum_eq_zero; intro s hs; by_contra hh; rw [Jets.hook_eq] at hh; split at hh
    next hi =>
       have hp:=farmhouse (P.X0.crop _ _ s) (citizenship f P.positive U) hh; have hk:= (mem_filter.mp hs).2; apply hk; have hg : ¬s⊆ halo r {i.1.1}:=fun h=> hP (h hp.2.2)
       exact (Fork.relic hg hp.2.1).le
    exact hh rfl
lemma vine_cost (r:ℕ)(hu: 0 ≤ u)(U:Grid f)(i j:A): ‖spore P r U i j - copies F ((T U)⁻¹) i j‖ ≤ Real.exp (-u*fossil r l)* q :=by
    let E' := Real.exp (-u*fossil r l)
    unfold spore; rw [linked (T U) _ (P.stable.sole _),←podium P U,Matrix.sum_apply, Matrix.sum_apply]; let W:=shortS (f:=f) r l
    rw [← Finset.sum_sdiff (subset_univ W) (f:=fun s=> ship P.X s (settled U) (F:=F) i j),add_comm (∑ x∈ Finset.univ \ W,_),←sub_sub,sub_self,zero_sub] -- syntax
    have h0:E' *duel P.Y i.1.1 j.1.1 u l≤ E'*q:=mul_le_mul_of_nonneg_left (packet P.X0 hu ..).2 (Real.exp_pos _).le
    rw [norm_neg]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun s:Support f=>Real.exp (-u*fossil r l)*(Run.rent u l s*P.Y i.1.1 j.1.1 s)) ?_).trans ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun s _ _=>mul_nonneg (Real.exp_pos _).le (mul_nonneg (Run.fair u l s).le (P.X0.crop i.1.1 j.1.1 s).1))).trans ?_))
    · intro s hs; rw [hook_eq]; split
      next hp =>
        have hz := (norm_nonneg _).trans ((P.X0.crop i.1.1 j.1.1 s).2.2.2.1 (settled U) (citizenship f P.positive _)); have hg: fossil r l ≤ coverNumber l s:= by
           apply Classical.byContradiction; intro ht; exact (mem_sdiff.mp hs).2 (mem_filter.mpr ⟨mem_univ _,ht⟩)
        apply (Cost.north ..).trans; exact ((P.X0.crop _ _ _).2.2.2.1 (settled U) (citizenship f P.positive U)).trans (by
           unfold Run.rent; rw [← mul_assoc,← Real.exp_add]; apply le_mul_of_one_le_left hz; exact Real.one_le_exp (by linarith only [mul_le_mul_of_nonneg_left hg hu]))
      rw [norm_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (fair ..).le (P.X0.crop ..).1)
    rw [← mul_sum]; exact h0
-- comparison to identity E6 patch costs
lemma verandah (hu:0 ≤u)(U:Grid f)(i j:A)(hw:beamAt (trunkFt i.1.1 r) U 1 w)(hz:0 ≤ w)(hδ:w <δ/2) :
    ‖spore P r U i j-spore P r 1 i j‖ ≤ q*(w/(δ/2)):=by
    let L:=shortS (f:=f) r l; let K:= w/(δ/2); have hQ := P.X0; have hp:= P.positive; have ht:0≤K:=div_nonneg hz (by positivity)
    unfold spore; rw [Matrix.sum_apply,Matrix.sum_apply,← sum_sub_distrib]; refine (norm_sum_le ..).trans ?_
    let Y:= P.Y i.1.1 j.1.1; have hv s:0 ≤ Y s:= (hQ.crop _ _ _).1
    apply le_trans (b:= ∑ s∈L,Y s*K)
    · apply sum_le_sum; intro s hs; rw [hook_eq,hook_eq]; by_cases hh:Y s=0
      · have hz(V:Grid f) : P.X i.1.1 j.1.1 s (settled V)=0:= norm_le_zero_iff.mp ((hQ.crop _ _ _).2.2.2.1 _ (citizenship f hp _) |>.trans hh.le)
        rw [hz,hz,sub_self,norm_zero,hh,zero_mul]
      split
      next hp' =>
         have hx : s⊆ trunkFt i.1.1 r:= by
            by_contra h; exact (mem_filter.mp hs).2 (show broad r l (Sum.inl s) from (Fork.relic h ((hQ.crop _ _ _).2.1 hh).1).le)
         exact (Cost.north (P.X _ _ s (settled U)- P.X _ _ s (settled 1)) _ _).trans (cruise (hQ.crop i.1.1 j.1.1 s) (Spice.mores hw hx) P.positive hδ hz)
      rw [sub_zero,norm_zero]; exact mul_nonneg (hv s) ht
    rw [← sum_mul]; have hx:=packet hQ hu i.1.1 j.1.1; refine mul_le_mul_of_nonneg_right (((sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun i _ _=>hv i)).trans ((sum_le_sum (fun i _=> le_mul_of_one_le_left (hv i) (market hu l i))).trans hx.2))) ht

end Rot
end YM.QCD.Leaf.Tee
