import YM.Eden.Rose
import YM.Poised.Reins
import YM.Elms.Spectral
/-! # Body covariance extension, rows raw to transported true. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eden
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range
open Finset YM.Bank Precision Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Classical Kronecker
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit QCD.Bloom QCD.Pine QCD.Grass
open Massive Massive.UV Patria Patria.Exposure Revolve TorusPCAC.Geometry TorusPCAC.Geometry.AxisB
open Lining Ferry Cylinder Elm Elm.SparK Elm.SparK.Arbor
variable {c f:Side}{N k m:ℕ}{I J:Type}[Fintype I][Fintype J]
variable (W:Walk)(p:Multi k)(x: Cover) (U: Grid c)(s:Signed)(P: EuPin)(A: Spike)
-- Bundle stencil.S
noncomputable def fadeF (v:Cover)(U:Grid c)(u:Walk) (j:Site c) : Bundle := if j=landsE c v u then ap c (capEdge v u) • touch (colour (haloW c v u U)) else 0
noncomputable def bladeU (v:Cover) (U:Grid c)(p: Multi k)(j:Site c): Bundle:= hears (fun w=>fadeF v U w j) (rider p)
noncomputable def rollsU (k:ℕ)(v:Cover)(U:Grid c): Matrix (SpinMode k) (Modes c 6) ℂ:= nacre (bladeU v U)
noncomputable def mood (k:ℕ)(v:Cover)(U:Grid c) := slab (rollsU k v U)
@[fun_prop] lemma fare_cts(i:Site c): Continuous (fun U:Grid c=>fadeF x U W i):= by unfold fadeF; split <;> fun_prop
@[fun_prop] lemma beam_cts(i:Site c): Continuous (fun U:Grid c=>bladeU x U p i):= by unfold bladeU hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum]; fun_prop
@[fun_prop] lemma hero_cts : Continuous (mood k x (c:=c)):=by apply continuous_matrix; rintro (i|i) (j|j); all_goals unfold mood slab rollsU; all_goals first | (simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₂,mstar]; simp only [imprints]; split <;> fun_prop) | exact continuous_const
lemma mark_heart : marked s p= limns s p:=by
    unfold limns Arise.vane UV.Free.steps; -- via List.prod attach map.V
    simp [List.finRange, Fin.prod_univ_succ, UV.marked,UV.signT,Arise.hue] -- inspect
lemma fade_spin (j:Site c) : fadeF x (pull s 0 U) W j* (Patria.prism s j • wave A) = wave A * fadeF (s.act x) U (tap s W) (s.act j):=by
    let w:=capEdge x W; -- inference
    have he: capEdge (s.act x) (tap s W) =s.act w:=by unfold w capEdge tap; have hp:= hale_last s W (0:Cover); rw [Signed.act_zero] at hp; rw [hp,Signed.act_add]
    have hf: landsE c (s.act x) (tap s W)=s.act (landsE c x W):=by unfold landsE; rw [he,← wrap_signed]
    unfold fadeF; split
    next hp=>
        rw [hf,hp,if_pos rfl,he, Matrix.smul_mul, Matrix.mul_smul,smul_smul, show ap _ _* Patria.prism _ _= _ from sheet_launch c w s]; unfold haloW; rw [Ferry.wind,Papyrus.scene,Lattice.travel_pull]; simp only [affine,Signed.act_zero,add_zero]; rw[Matrix.mul_smul]; congr 1; exact (Lat.interlace ..).eq
    next hp=> rw[hf, if_neg (s.act_injective.ne hp),Matrix.zero_mul,Matrix.mul_zero]
lemma travels_r {K : Rhythm}(f: Walk→Bundle): hears f (torch s K)=hears (fun i=>f (tap s i)) K:=by induction K using Finsupp.induction_linear with|zero=>simp|add u v h hp=>rw[map_add,map_add,map_add,h,hp]|single i a=>simp[torch,hears]
lemma colors_wave (j:Site c) : bladeU x (pull s 0 U) p j * (Patria.prism s j • wave A) =((marked s p:ℂ) • wave A)* bladeU (s.act x) U (hem s p) (s.act j):=by
    unfold bladeU; rw [show hem s p=gybe s p from rfl, rideE,map_smul,travels_r,← mark_heart]; let Z:=wave A; let S:=marked s p; let f(i:Walk):=fadeF x (pull s 0 U) i j; let g(i:Walk):=fadeF (s.act x) U (tap s i) (s.act j); let M(K:Rhythm):=hears f K; let J:=rider p; let N':=hears g J
    change M J * _ = ((S:ℂ) • Z)*(S • N'); rw [Matrix.smul_mul,show S • N'=(S:ℂ) • N' from Complex.coe_smul ..,Matrix.mul_smul Z,smul_smul, ← Complex.ofReal_mul, show S*S=1 from marked_sq .., Complex.ofReal_one,one_smul]
    unfold M J N' hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum, Matrix.sum_mul,Matrix.mul_sum, Matrix.smul_mul,Matrix.mul_smul Z]; exact sum_congr rfl (fun i h=> congr_arg ((rider p i) • ·) (fade_spin ..))
lemma roll_pin(h:P.Lifts s) : rollsU k x (pull s 0 U)*Action.moved s A=UV.turned P (wave A)*rollsU k (s.act x) U:=by
    unfold rollsU; rw [roller,ink_pin s P h]; 
    let W:= (Signed.actEquiv (R:=Per c) s).toEquiv; let X:=bladeU x (pull s 0 U) (k:=k); let Y:=bladeU (s.act x) U (k:=k); let J:=fun j:Site c=>prism s j • wave A; let Z:=fun i:Multi k=> (marked s i:ℂ) • wave A; let V:= hem s (d:=k); exact (Lining.spar_after W J X).trans ((congr_arg nacre (funext fun i=> funext fun j=>by obtain ⟨j,rfl⟩:=W.surjective j; rw [W.symm_apply_apply]; exact colors_wave ..)).trans (Lining.spar_mul V Z Y).symm)
-- applies bars too all transformations.
end YM.QCD.Eden
#print axioms YM.QCD.Eden.roll_pin
