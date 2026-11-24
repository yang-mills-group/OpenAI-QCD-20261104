import YM.DawnS.Stay
import YM.DawnS.Coal
import YM.DawnS.Silver
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
local notation "I₀"=>Complex.I
local notation "P"=> RingS
local notation "Ω"=>muS
variable {d:ℕ}
noncomputable def listP (p:chit d):List SpaceAxis:=(List.finRange 3).flatMap fun i=> List.replicate (power p.val i.castSucc) i
lemma running(p:chit d):steps p.val= toAxes (listP p):=by
     unfold steps toAxes listP; rw[List.map_flatMap]; have h : (List.finRange 4)= (List.finRange 3).map Fin.castSucc ++ [K]:= rfl --?
     rw[h,List.flatMap_append,List.flatMap_map]; simp [p.property]
noncomputable abbrev phaseG (p:chit d)(v:Bool)(z:P):ℂ:= (if v then -I₀ else I₀)^(listP p).length * ((stepTheta z (listP p):ℝ):ℂ)
noncomputable def gleam (v:Bool)(p:chit d)(r:ℝ)(z:PR):ℂ:= ((↑(z.1/r):ℂ) ^ (listP p).length) * phaseG p v z.2
lemma fluidG(p:chit d)(v:Bool):Continuous (phaseG p v):= continuous_const.mul (Complex.continuous_ofReal.comp (step_cont _))
lemma gleams(v:Bool)(p:chit d)(r:ℝ): Continuous (gleam v p r):=((Complex.continuous_ofReal.comp (continuous_fst.div_const r)).pow _).mul ((fluidG p v).comp continuous_snd)
noncomputable def dotsG(r:ℝ):Points 2:=points ![0,prelude r]
lemma distinct(r:ℝ)(h:0<r): dotsG r∈ conf 2:=by
    have hp: prelude r≠0:= swept r h.ne'; change Injective ![0,prelude r]; intro i j he; fin_cases i <;> fin_cases j <;> first|rfl|exfalso; apply hp; simpa using he.symm|exfalso; apply hp; simpa using he
local notation "KK" d:arg r:arg => chime (fun _ : Fin 2 =>d) (dotsG r)
noncomputable def sigL (r:ℝ) : beam d →ₛₗ[starRingEnd ℂ] (beam d→ₗ[ℂ]ℂ):=(LinearMap.compl₂ (.id) (rifle (fun _:Fin 2=>d) 1)).comp (((unionB (KK d r)).comp (rifle _ 0)).comp (adjLine d)) -- syntax check. easier explicit
set_option quotPrecheck false
variable (p q:chit d) (a b:Pinor) (i j:Hue) (k t:Flavor 6)(r:ℝ)(hr:0<r)
local notation "A"=>((p.val,a,i),k)
local notation "N"=> ((q.val,b,j),t)
local notation "η"=> sigL (d:=d) r
local notation "fP"=>lantern
-- cross vanishing
include hr
lemma across : sigL r (upL A) (dnL N)=0:=by
      change unionB (KK d r) (rifle _ 0 (adjLine d (upL A))) (rifle _ 1 (dnL N))=_; rw[alum]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; refine sum_eq_zero fun s _=> ?_
      change _ * unionB (KK d r) (rifle _ 0 (dnL ((p.val,s,i),k))) (rifle _ 1 (dnL ((q.val,b,j),t)))=_; unfold dnL; rw[mounted,mounted,sector (dotsG r) (distinct r hr)]; simp [UV.Free.pair]
lemma toward : sigL r (dnL A) (upL N)=0:=by
      change unionB (KK d r) (rifle _ 0 (adjLine d (dnL A))) (rifle _ 1 (upL N))=_; rw[amel]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; refine sum_eq_zero fun s _=> ?_
      change _ * unionB (KK d r) (rifle _ 0 (upL ((p.val,s,i),k))) (rifle _ 1 (upL ((q.val,b,j),t)))=_; unfold upL; rw[mounted,mounted,sector (dotsG r) (distinct r hr)]; simp [UV.Free.pair]
lemma cusp : sigL r (upL A) (upL N)= ∑ x:Pinor,gamma K x a * Free.leg N ((p.val,x,i),k) (prelude r) 0:=by
      change unionB (KK d r) (rifle _ 0 (adjLine d (upL A))) (rifle _ 1 (upL N))=_; rw[alum]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; refine Finset.sum_congr rfl fun s _=> ?_
      unfold upL dnL; rw[mounted,mounted,sector (dotsG r) (distinct r hr)]; simp [UV.Free.pair,dotsG, sig, p.property]
lemma cape : sigL r (dnL A) (dnL N)= ∑ x:Pinor,- gamma K a x * Free.leg ((p.val,x,i),k) N 0 (prelude r):=by
      change unionB (KK d r) (rifle _ 0 (adjLine d (dnL A))) (rifle _ 1 (dnL N))=_; rw[amel]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; refine Finset.sum_congr rfl fun s _=> ?_
      unfold upL dnL; rw[mounted,mounted,sector (dotsG r) (distinct r hr)]; simp [UV.Free.pair,dotsG, sig, p.property]
end YM.DawnS
