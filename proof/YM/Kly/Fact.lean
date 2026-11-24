import YM.Kly.Cape
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
variable (hA: B.Comparison (bloom P H w))
def chart (Z:F.Kernel)(y:E4): F.W→ₛₗ[starRingEnd ℂ] F.W→ₗ[ℂ] ℂ:=by
       let L(x u:F.W):= Z 2 (points ![0,y]) (![F.adj timeAxis x,u]); let W:= Z 2 (points ![0,y]); let f(v:F.W):= W.toLinearMap (![F.adj t₀ v,0]) 1
       have ht(v u:F.W):f v u=L v u:=by apply congr_arg W; ext1 i; fin_cases i<;>simp -- mess
       refine {toFun:= f,map_add':=fun x y'=>LinearMap.ext fun z=>?_,map_smul':=fun c y'=>LinearMap.ext fun z=>?_}
       · simp only[LinearMap.add_apply,ht]; unfold L; rw[map_add]; let v:= W.toLinearMap (![0,z]) 0; have hx(x:F.W): W (![x,z])= v x:=by apply congr_arg W; ext1 i; fin_cases i <;> simp
         exact (hx _).trans ((map_add v _ _).trans (by rw [←hx,←hx]))
       simp only[LinearMap.smul_apply,ht]; unfold L; rw [map_smulₛₗ]; let v:= W.toLinearMap (![0,z]) 0; have hx(x:F.W): W (![x,z])=v x:=by apply congr_arg W; ext1 i; fin_cases i<;>simp
       exact (hx _).trans ((map_smul v _ _).trans (by rw[←hx]))
-- need expose ht
lemma charter (Z:F.Kernel)(x y:F.W)(s:E4): chart Z s x y= Z 2 (points ![0,s]) (![F.adj timeAxis x,y]):=by
       apply congr_arg (Z 2 _); ext1 i; fin_cases i<;>simp
include P H Y E
lemma trueP (r:ℝ)(h:0<r) : 0 ≤ chart Sα (r • basis t₀) x x:=by
       let p: E4:= (r/2) • basis t₀; let u:Future F t₀ := ⟨[(p,x)], ⟨locations.mpr (by simp), fun i hi=>by rw[List.mem_singleton.mp hi]; simp [p,h]⟩⟩; have he:= realPr P H Y E w (fun _ : Fin 1=>u) (fun _=> 1)
       have hp : Points.across p (points ![-p,p]) = points ![0,r • basis t₀]:=by ext1 i; fin_cases i<;> simp[p,← add_smul]
       have hs: reflect u.val t₀++u.val=realize (![F.adj t₀ x,x]) (points ![-p,p]):=by
               rw [reflectedPoint]; change [(Ortho.move _ _,_), (p,x)]=_; have hz:Ortho.move (Signed.reflect t₀) p= -p:=by unfold p; ext1 i; by_cases hx:i=t₀ <;> simp[hx,Signed.mirrored]
               unfold realize; dsimp only; rw[hz]; simp [List.ofFn_succ]
       rw [charter,← hp,Points.across,show Sα 2 _ _= _ from travels P H (points ![-p,p]) (![F.adj t₀ x,x]) w ((realized ..).mp (hs ▸ twoSides u.property u.property)) p,←readAt,←hs]; change 0≤pointMoment Sα _; simpa only[Fields.gram,Fin.sum_univ_one,star_one,one_mul,mul_one] using he
include U hA
variable (d:ℕ)
noncomputable def yiel (K:F.Kernel)(r:ℝ)(d k:ℕ): UV.Free.Symbol d →ₛₗ[starRingEnd ℂ] UV.Free.Symbol d →ₗ[ℂ]ℂ:=by
       let L:= (F.level d).subtype.comp (B.frame k d).toLinearMap
       exact {toFun:=fun x=> (chart K (r • basis t₀) (L x)).comp L,map_add':=fun x y=>LinearMap.ext fun z=>by rw [LinearMap.add_apply, LinearMap.comp_apply,map_add,map_add,LinearMap.add_apply]; rfl,map_smul':=fun c x=>LinearMap.ext fun z=>by rw [LinearMap.smul_apply,LinearMap.comp_apply,map_smul,map_smulₛₗ,LinearMap.smul_apply]; rfl }
noncomputable abbrev invoices (k:ℕ):= yiel (B:=B) Sα (B.radius k) d k
lemma boxP (x y:Label d): Tendsto (fun k=> invoices P H w (B:=B) d k (projection x) (projection y)) atTop (𝓝 (wick (fun _ : Fin 2 =>d) (points ![0,basis timeAxis]) (![C.sym.adj d t₀ x,y]))) :=by
         let L:=points (![0,basis t₀]); have hm:L∈conf 2:=by have he:basis timeAxis ≠ 0:= norm_ne_zero_iff.mp ((basis_norm timeAxis).symm ▸ one_ne_zero); intro i j; fin_cases i <;> fin_cases j <;> simp only [L,points_apply] <;> simp[he,he.symm]; -- inspect
         have he:= hA.point 2 (fun _=>d) (![C.sym.adj d t₀ x,y]) L hm; apply he.congr'; refine Eventually.of_forall fun k=>?_ ; let R:=B.radius k; change Sα 2 _ _=chart Sα (R • basis t₀) (B.choice k x) (B.choice k y); rw[charter]; apply congr_arg₂ (fun x:Points 2=>fun p:Fin 2→F.W=> Sα 2 x p); · ext i; fin_cases i<;> simp[L,R]
         ext1 i; fin_cases i; exact U.reality k d t₀ x; rfl
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.boxP
