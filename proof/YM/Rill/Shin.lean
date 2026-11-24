import YM.Rill.Print
/-! Gram power calculus. Keep explicit lists, not completion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Strip Petals Finset
variable {C:Sequence} {P:Calibration C}(hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {Q: Choir}(L:Pollens P Q)(a:Axis) {β e:ℝ}(hp:C.Path β e)
variable {n m:ℕ}
-- fixed Gram comb.
namespace Strip
noncomputable abbrev reach (l g:Strip Q):= Strip.tone (oppositeS L a l ++ g)
noncomputable def valley (l: Fin n → Strip Q)(k: Fin m→Strip Q)(v:Fin n→ℂ)(z:Fin m→ℂ):ℂ:= ∑ i,∑ j,star (v i)*reach L a (l i) (k j)* z j
variable (G:∀ d,Cottage P d)(hr:Sway C.S)(H:Q.Harmony P φ)
variable {v:Strip Q}{x:Strip Q}
include hQ hp H hφ
lemma lakes (hv:Sunny v a)(hx:Sunny x a): reach L a v x=star (reach L a x v):=by unfold reach; rw [← console hQ hφ L _ a hp H (aheadV L a x v hx hv)]; rw [nodes,twisted L _ a H.h] -- binder. hx.
include G hr
variable (l:Fin n→Strip Q)(g:Fin m→Strip Q)(v':Fin n→ℂ)(w:Fin m→ℂ)
lemma signal (hL:∀ i,Sunny (l i) a):0 ≤ valley L a l l v' v':= rpTrue hQ hφ L a hp G hr H l hL v'
set_option maxHeartbeats 460000 in
lemma lights (hL:∀ i,Sunny (l i) a)(h':∀ i,Sunny (g i) a): ‖valley L a l g v' w‖^2 ≤ ‖valley L a l l v' v'‖*‖valley L a g g w w‖:=by
     let R:=Fin.append l g; have h(i):Sunny (R i) a:=by induction i using Fin.addCases <;> simp only [R,Fin.append_left,Fin.append_right] <;> first | apply hL| apply h'
     have hx:= signal hQ hφ L a hp G hr H l v' hL; have hy:=signal hQ hφ L a hp G hr H g w h'; have he:valley L a g l w v'= star (valley L a l g v' w):=by
          unfold valley; rw [star_sum,Finset.sum_comm]; refine sum_congr rfl (fun i _=>?_ ); rw [star_sum]; refine sum_congr rfl (fun j _=>?_); rw [star_mul,star_mul,star_star,lakes hQ hφ L a hp H (h' j) (hL i)]; ring -- rew star argument risk cyclic
     refine Cells.schwarz hx hy (fun z=>?_); let X:=star z; let F:=Fin.append v' (X • w); have hz:= signal hQ hφ L a hp G hr H R F h; let Wz(p q:ℂ)(t:ℂ):= star p*t*q
     refine hz.trans_eq ?_; rw [←he]; unfold valley F R; rw[Fin.sum_univ_add]; simp_rw [Fin.sum_univ_add]; simp only [Fin.append_left,Fin.append_right,Pi.smul_apply,smul_eq_mul,star_mul,X,star_star,Finset.sum_add_distrib, Finset.mul_sum]
     -- multiply terms regroup
     have h1 :∀ a b c:ℂ, a*b*(star z*c)=star z * (a*b*c):=fun a b c=>by ring
     have h2:∀ a b c:ℂ,a*z*b*c=z*(a*b*c):=fun a b c=>by ring
     -- inspect
     have h3:∀ a b c:ℂ,a*z*b*(star z*c)=(z*star z)*(a*b*c):=fun a b c=>by ring
     simp_rw [h3,h2,h1]; abel

end Strip
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Strip.lights
