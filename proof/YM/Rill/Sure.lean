import YM.Rill.Hill
/-! First field detection with genuine reflected pair across strict cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Strip Petals
variable {C:Sequence} {P:Calibration C}(hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {Q: Choir}(L:Pollens P Q)(a:Axis) {β e:ℝ}(hp:C.Path β e)
variable (G:∀ d,Cottage P d)(hr:Sway C.S)(H:Q.Harmony P φ)
include hp H hQ hr hφ G
set_option maxHeartbeats 510000 in
lemma faithfulW (v:Q.W)(hv:v≠0): ∃ r:ℝ,0<r ∧ 0<Q.total 2 (points ![0,r • basis a]) ![L.adj a v,v]:=by
    obtain ⟨x,hx,w,hP⟩:= H.h.listens v hv; let R:=x a/2; let θ:= R • basis a; let p:= x-θ; let t:= L.adj a; have hR:0 < R:=half_pos (hx _); obtain ⟨u,hu⟩:= t.surjective w
    let V:Strip Q:=[(θ,u)]; let W:Strip Q:=[(p,v)]; have he:θ a=R:= (by simp [θ]); have hw:p a= R:=by change x a- θ a= _; rw[he]; unfold R; ring
    have hpV: Sunny V a:=by refine ⟨(spots _).mpr (by simp [V]),?_⟩; intro i hi; simp only [V,List.mem_singleton] at hi; rw[hi,he]; exact hR
    have hpW: Sunny W a:=by refine ⟨(spots _).mpr (by simp [W]),?_⟩; intro i hi; simp only [W,List.mem_singleton] at hi; rw [hi,hw]; exact hR
    have hf (V W:Strip Q): valley L a (fun _: Fin 1=> V) (fun _: Fin 1=> W) (fun _=>1) (fun _=>1)=tone (oppositeS L a V++ W):=by unfold valley; simp
    let T' :=oppositeS L a V; let U:= oppositeS L a W
    have hb: Strip.shifting (T'++W) θ=[(0,w),(x,v)]:=by
         have hh:Ortho.move (Signed.reflect a) θ= -θ:=by ext i; by_cases hy:i=a <;> simp [hy,Signed.mirrored,θ]
         change _=[_,_]; simp only[T',V,W,Strip.shifting,oppositeS,List.reverse_singleton,List.map_cons,List.map_nil,List.cons_append,List.nil_append]; rw [hh,show L.adj a u=w from hu,neg_add_cancel,show p+θ=x from sub_add_cancel ..]
    have hS: tone (T'++ W)=Q.total 2 (points ![0,x]) ![w,v]:=by
         rw[← migrates hQ hφ (T'++W) θ hp H (aheadV L a V W hpV hpW),hb]; unfold Strip.tone; congr 1
         · congr 1; ext1 i; fin_cases i <;> rfl
         ext1 i; fin_cases i <;> rfl
    have hs := lights hQ hφ L a hp G hr H (fun _:Fin 1=>V) (fun _:Fin 1=>W) (fun _=>1) (fun _=>1) (fun _=>hpV) (fun _=>hpW)
    have hl : 0 < tone (U ++ W) := by
        refine lt_of_le_of_ne ?_ ?_; · rw [← hf W]; exact signal hQ hφ L a hp G hr H _ _ (fun _=>hpW)
        intro he; simp_rw[hf] at hs; rw [hS, he.symm, norm_zero,mul_zero] at hs; exact not_le_of_gt (pow_pos (norm_pos_iff.mpr hP) 2) hs
    let b:=-(Ortho.move (Signed.reflect a) p); let r:=x a; have hz:p+b= r • basis a:=by
         unfold b; ext i; by_cases he:i=a; · subst i; simp only [PiLp.add_apply,PiLp.neg_apply, Signed.mirrored,↓reduceIte,neg_neg,hw]; simp [R, r]
         simp [he,Signed.mirrored]
    have hZ: Strip.shifting (U++W) b=[(0,L.adj a v),(r • basis a,v)]:=by simp only[U,W,Strip.shifting,oppositeS,List.reverse_singleton,List.map_cons,List.map_nil,List.cons_append,List.nil_append,hz]; simp[b]
    refine ⟨r,hx a,?_⟩; change 0<Q.total 2 (points ![0,r • basis a]) ![_,_]; rw [←migrates hQ hφ (U++W) b hp H (aheadV L a W W hpW hpW),hZ] at hl; refine hl.trans_eq ?_; unfold Strip.tone; congr 1
    · congr 1; ext1 i; fin_cases i <;> rfl
    ext1 i; fin_cases i <;> rfl
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.faithfulW
