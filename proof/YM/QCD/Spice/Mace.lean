import YM.QCD.Spice.Cake
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
-- Chop P Upper single AUTH-W charge, unaffected rotations. assume distance in color directly; furnish CHORD dist from conditioning.
def beamAt (X:Support f)(U V:Grid f)(w:ℝ): Prop:=∀ i:Edge (Site f), i.1∈X→i.1+step i.2 ∈ X → ‖colour (U i)-colour (V i)‖ ≤ w
lemma mores {X Y:Support f}{U V:Grid f}(h:beamAt X U V w)(ht:Y⊆X): beamAt Y U V w:=fun i hi hx=> h i (ht hi) (ht hx)
noncomputable def seenX (X:Support f)(U V:Grid f):Grid f:=fun i=> if i.1∈X∧ i.1+step i.2∈X then U i else V i
lemma films (X:Support f)(U V:Grid f)(h:beamAt X U V w)(hw:0≤w):let W:= seenX X U V; Agrees X U W ∧ ‖settled W-settled V‖≤ w:=by
   intro W; have he i : ‖colour (W i)-colour (V i)‖≤ w:=by 
       unfold W seenX; split
       next hp=>exact h i hp.1 hp.2
       next _=>rw [sub_self,norm_zero]; exact hw
   refine ⟨fun i hi hx=> Eq.symm (if_pos (And.intro (show i.1∈X from hi) (show i.1+step i.2∈X from hx))), max_le ((pi_norm_le_iff_of_nonneg hw).mpr he) ((pi_norm_le_iff_of_nonneg hw).mpr fun i=>?_)⟩
   change ‖star (colour (W i))-star (colour (V i))‖≤w; rw [← star_sub,norm_star]; exact he _
lemma cruise {X:Support f}{U V:Grid f} {Z:Pulse f→Bundle}{o₁ o₂: Site f}(h: Crop o₁ o₂ v X Z t) (hp:beamAt X U V w)(hv:0<v)(he:w<v/2)(hw:0 ≤ w): ‖Z (settled U)-Z (settled V)‖ ≤ t*(w/(v/2)):=by
   obtain ⟨hx,hh⟩:=films X U V hp hw; let Sz:= seenX X U V
   have ht:∀ u ∈ Metric.ball (settled V) v,u∈ Kingdom f v:=fun i hi=> Set.mem_iUnion.mpr ⟨V,hi⟩
   have hG: settled Sz∈ Metric.ball (settled V) (v/2):= Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hh.trans_lt he)
   rw [show Z (settled U) = Z (settled Sz) from h.2.2.2.2.1 U Sz hx]; exact (lastwig Z hv (fun i hi=> h.2.2.1 _ (ht i hi)) (fun i hi=> h.2.2.2.1 _ (ht i hi)) hG).trans ((mul_le_mul_of_nonneg_left hh (div_nonneg h.1 (half_pos hv).le)).trans_eq (by ring))
private lemma diffS (U V:Grid f)(b:ℕ)(s:Support f)(hp:beamAt s U V w) (hv:w<δ/2)(hw:0≤w): let Q: Water c f F:= longP P.Z P.V b (settled U) s - longP P.Z P.V b (settled V) s
     ∑ i:Keys f F,∑ j:Keys c F,‖Q i j‖ ≤ (fingers F^2 *P.sumS b s)*(w/(δ/2)) :=by
   intro Q; let Bz:= w/(δ/2); unfold Q; simp only [Matrix.sub_apply]; rw [Fintype.sum_sum_type]; simp_rw [Fintype.sum_sum_type,longP,foamLR,foamRL,sub_zero,norm_zero,sum_const_zero,add_zero,zero_add]; rw [← sum_add_distrib, mul_assoc, sumS, sum_mul]; simp_rw [← sum_add_distrib,sum_mul]
   apply padS; intro i j; rw [foamI,foamR,foamI,foamR]; unfold headF; by_cases he:s∈satZip i.1.1 b; swap; · by_cases h:i.2=j.2 <;> simp [he,h]
   simp only [he,if_true]; by_cases hh:i.2=j.2; swap
   · simp only [Ne.symm hh,hh,if_false,sub_zero,norm_zero,add_zero]; exact mul_nonneg (add_nonneg (P.Z0.crop ..).1 (P.V0.crop ..).1) (div_nonneg hw (half_pos P.positive).le)
   simp only [hh,if_true]; rw [add_mul]; exact add_le_add ((Cost.north (P.Z i.1.1 j.1.1 s (settled U)-P.Z i.1.1 j.1.1 s (settled V)) ..).trans (cruise (P.Z0.crop ..) hp P.positive hv hw)) ((Cost.north (P.V j.1.1 i.1.1 s (settled U)- P.V j.1.1 i.1.1 s (settled V)) ..).trans (cruise (P.V0.crop ..) hp P.positive hv hw))
private lemma diffI (U V:Grid f)(b:ℕ)(s:Support f)(hp:beamAt s U V w)(hv:w<δ/2)(hw:0≤w): let Z:Matrix A A ℂ:= ship P.X s (settled U)-ship P.X s (settled V); ∑ i:A,∑ j,‖Z i j‖ ≤ (fingers F^2 * P.sumX s)*(w/(δ/2)):=by
    intro Z; rw [mul_assoc,sumX,sum_mul]; simp_rw [sum_mul]; apply paddleB b s 0; intro i j; have h:= cruise (P.X0.crop (headF i) (headF j) s) hp P.positive hv hw; unfold Z; rw [Matrix.sub_apply,hook_eq,hook_eq]; split
    · exact (Cost.north (P.X _ _ s (settled U)-P.X _ _ s (settled V)) ..).trans h
    rw [sub_self,norm_zero]; exact (norm_nonneg _).trans h
lemma plumes (F b:ℕ)(U V:Grid f)(i:Tr f) (h:beamAt (roomK i) U V w)(hp:0<x)(hq:0<y)(hw:0≤w)(hv:w<δ/2): Pledge (rateF c f F x y) (mapQ P.X P.Z P.V b i (settled U) - mapQ P.X P.Z P.V b i (settled V)) (terra P F b x y i*(w/(δ/2))) :=by
    cases i
    next i=>
      let K:Matrix (Modes f F) (Modes f F) ℂ:=ship P.X i (settled U); let J:Matrix (Modes f F) (Modes f F) ℂ:=ship P.X i (settled V)
      let H:=ha c f F; change Pledge _ (pond H K-pond H J) _; rw [show pond H K-pond H J=pond H (K-J) from ?_]; rotate_left
      · suffices h:pond H (K-J) + pond H J=pond H K by rw [← h]; abel
        rw [← Jets.pond_add,sub_add_cancel]
      apply (parent (K-J) _ (fun i=> rate_ok i hp hq) H).bumps
      unfold Ledge.pawn; simp only [met,pet,H,ha,rateF,wagesA,←sum_mul,← sq]; apply (mul_le_mul_of_nonneg_right (diffI (F:=F) P U V b i h hv hw) (sq_nonneg _)).trans_eq; unfold terra; dsimp; ring
    next i=>
      let K:Water c f F:= longP P.Z P.V b (settled U) i; let J:Water c f F:= longP P.Z P.V b (settled V) i
      rw [show mapQ P.X P.Z P.V _ (.inr i) (settled U)-_=bark (K-J) from ?_]; rotate_left
      · change barkG _ _ K-barkG _ _ J=barkG _ _ (K-J); unfold barkG; rw [← sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [← sum_sub_distrib]; exact sum_congr rfl (fun j _=> (sub_smul ..).symm)
      apply (prices (K-J) _ (fun i=> rate_ok i hp hq) ..).bumps
      unfold barksP; simp only [rateF,wagesA,wagesB,←sum_mul]; apply (mul_le_mul_of_nonneg_right (diffS P U V b i h hv hw) (by positivity)).trans_eq; unfold terra; dsimp; ring
end YM.QCD.Spice
