import YM.Tarn.Grade
/-! Gram pre-terms in mixed Grass order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set TensorProduct HarmonyF Strip Petals
open Poised Poised.Plans Poised.Plans.Stamp QCD.Grass Needle
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q: Choir} {φ:ℕ→ℕ}(h:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)(hQ:P.System)
namespace Harmony
variable (L:Pollens P Q)(l m:Strip Q)(x y:E4 × Q.W)
include hp h hφ hQ
set_option maxHeartbeats 370000 in
lemma swapS (p q:Bool)(hv: distinct (l++x::y::m))(hx:markedW L p x.2)(hy:markedW L q y.2): tone (l++x::y::m)= (if p&&q then -1 else 1)*tone (l++y::x::m):=by
    obtain ⟨u,U,hU⟩:= seeks hp h hφ l none; obtain ⟨v,V,hV⟩:= seeks hp h hφ m none
    obtain ⟨d,s,hh,hS⟩:=tickets h L none hx; obtain ⟨b,t,hk,hT⟩:=tickets h L none hy
    let X:=planted P x.1 φ ⟨d,s⟩; let Y:=planted P y.1 φ ⟨b,t⟩; let F:= u++X::Y::v; let K:= u++Y::X::v; have hP:List.Perm F K:= List.Perm.append_left _ (List.Perm.swap ..); have hX: sight none Q X=x:=Prod.ext rfl hh; have hY: sight none Q Y=y:=Prod.ext rfl hk
    have hd : petals Q none F=l++x::y::m:=by change List.map _ (_++_)= _; rw [List.map_append,List.map_cons,List.map_cons]; exact congr_arg₂ (·++·) U (congr_arg₂ List.cons hX (congr_arg₂ List.cons hY V))
    have he : petals Q none K=l++y::x::m:=by change List.map _ (_++_)= _; rw [List.map_append,List.map_cons,List.map_cons]; exact congr_arg₂ (·++·) U (congr_arg₂ List.cons hY (congr_arg₂ List.cons hX V))
    have hi:distinct (petals Q none F):= hd.symm ▸ hv; have hc:distinct (petals Q none K):=(spots _).mpr ((hP.map (sight none Q)|>.map Prod.fst).nodup_iff.mp ((spots _).mp hi))
    have hZ(z): z∈F→ Atlas C P φ z:=by -- syntax
         intro hz; rcases List.mem_append.mp hz with hp|hp'; exact hU _ hp; simp only [List.mem_cons] at hp'; rcases hp' with rfl|rfl|hy; exact aliveP hp hφ _ _; exact aliveP hp hφ _ _; exact hV _ hy
    rw [←hd, ←he]; apply tendsto_nhds_unique (reaches h F none hi hZ); refine (((reaches h K none hc (fun z hz=>hZ z (hP.mem_iff.mpr hz))).const_mul _).congr' ?_); filter_upwards [acted hφ hQ X none hS,acted hφ hQ Y none hT] with i hi H
    let A:=(C.A (φ i)).regulator.average; let f(U:Petal P):=signalW none U φ i; let c:ℂ:= if p&&q then -1 else 1
    have ht': c • (f Y*f X)= f X*f Y:=by
         ext1 z; change c • (f Y z*f X z) = f X z*f Y z; have h:= (H z).swap (hi z); rw [Bool.and_comm] at h; unfold c; split
         next H=> rw [if_pos H] at h; rw [neg_one_smul,h]
         next H=> rw[if_neg H] at h; rw [one_smul,h]
    change c • A (K.map f).prod=A (F.map f).prod; rw [←map_smul]; apply congr_arg A; unfold F K; simp only [List.map_append,List.map_cons,List.prod_append,List.prod_cons]; rw [← mul_smul_comm, ← mul_assoc (f Y) (f X),← smul_mul_assoc, ht',mul_assoc]
end Harmony
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Harmony.swapS
