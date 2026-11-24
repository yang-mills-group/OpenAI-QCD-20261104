import YM.QCD.Orbit.Choir

/-!
# supply from all input stages at given gauges, before switching periods or
coefficients. Budget depends on L and clip/stage; exposes arrays at same width
across entire meshes. does not include inheritance receipt to ATTACHED bloomed paths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Orbit.Birth
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine Rudder
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {T : Type*} {j k N : ℕ}{P : T→Flight j k}{Δ O Q K : ℝ}{C : KernelChoices}{p : Clip}{H : T→PathData su}
    {S : T→SparkMesh} (Z : ∀ i, Place (P i) C (S i) (H i) p O Q)
variable (B:Plan j)(L:Plan k)
variable (E:Patch) (hE:∀ i,(P i).patch=E) (M: Push.Uniform.Before su O Q E.J C N)
local notation "X"=>stand S P C
variable {D: ∀ (_:T)(f:Side), Grid f→ Sheet f} 
include hE M
lemma qualified (hV : ∀ y:T,Vital (D y)) (hU : ∀ Y:Quay X C E p M,(X).League (A:=true) (B:=true) fun i x=> D i.1 _ (Y.forge i x)) (i:T): Clan (S i) (launch (Z i) B L (D i)) ∧∀ j,Noble (launch (Z i) B L (D i) j):=by
  apply phase (Z i) L (hV i)
  obtain ⟨w,d,h,hD,Hw⟩:= on_bills Z B L E hE M hV hU
  intro j; exact matrix_g fun k l=> (Hw i j k l).host

-- first newborn
lemma gemology (hV : ∀ y:T,Vital (D y)) (hU : ∀ Y:Quay X C E p M,(X).League (A:=true) (B:=true) fun i x=> D i.1 _ (Y.forge i x)) : ∃ r d, 0<r ∧ 0≤d∧∀ i:T,∃ V:Fruited (Snug 1)→Bloom 1,
    Fractal V r d∧ Vital (dust V) ∧ ∀ j,Tender (launch (Z i) B L (D i) j) (castF (dust V _)) 2:=by
  obtain ⟨w,d,h,hD,Hw⟩:=on_bills Z B L E hE M hV hU
  obtain ⟨r,b,hr,hb,Hx⟩:= Eternal 1 (by decide) h hD; refine ⟨r,b,hr,hb,fun i=>?_⟩
  have he:= qualified Z B L E hE M hV hU i
  have hx n: EmptyThrough (launch (Z i) B L (D i) n) 1:=by
    intro j hj; interval_cases j; ext x y; rw [iteratedFDeriv_zero_apply, shoots _ L (hV i)]; simp
  obtain ⟨P,hK,hp,Hk⟩:= Hx _ _ he.1 (Hw i) hx he.2; exact ⟨_,hK,Vital.tribute hK hr (by decide) hp, Hk⟩

-- second, now Fout1 provided and F4 gauges allowed. uses uniform prices.
lemma geology (hV : ∀ y:T,Vital (D y)) (hU : ∀ Y:Quay X C E p M,(X).League (A:=true) (B:=true) fun i x=> D i.1 _ (Y.forge i x)) (U:T→Type) (A:∀ i,U i→Bloom 1) {r c:ℝ} (hr:0<r)(he:∀ i,Fractal (A i) r c)(hK:∀ i,Vital (dust (A i)))
    (hf:∀ i j,Tender (launch (Z i) B L (D i) j) (castF (dust (A i) _)) 2):
    ∃ b d, 0<b ∧0≤d∧∀ i:T,∃ V:Fruited (Snug 2)→Bloom 2,
    Fractal V b d∧ Vital (dust V) ∧ ∀ j,Tender (launch (Z i) B L (D i) j - castF (dust (A i) _)) (castF (dust V _)) 3:=by
  rcases isEmpty_or_nonempty T with hT|hT; · exact ⟨1,1,zero_lt_one,zero_le_one,fun i=> isEmptyElim i⟩
  obtain ⟨i⟩:=hT
  obtain ⟨w,d,h,hD,Hw⟩:=on_bills Z B L E hE M hV hU
  obtain ⟨u,b,hu,hb,Hb⟩:= attainable 1 hr c; have hm:= lt_min h hu
  have hc : 0≤c:= (tsum_nonneg (fun j=> ((A i j).price_nn).trans ((A i j).paidUp hr.le))).trans (he i).bill
  have hv:= mul_nonneg hb hc
  obtain ⟨r',B',hr',hB',Hp⟩:= Eternal 2 (by decide) hm (add_nonneg hD hv)
  refine ⟨r',B',hr',hB',fun i=>?_⟩
  have he' := qualified Z B L E hE M hV hU i
  have hΦ := he'.1.less (grove (he i) hr _)
  let F (j) := castF (dust (A i) ((S i).n j)); let I:= launch (Z i) B L (D i)-F
  have hh j : Eyrie.glyph (traceG ((S i).n j)) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (I j) (min w u) (d+b*c):=by
    have hj:= ((Hw i j).reduces hm (min_le_left ..) hD le_rfl).plus (((Hb (U i) (A i) (he i) _).reduces hm (min_le_right ..) hv le_rfl).minus)
    rw [show I j=launch (Z i) B L (D i) j+ -F j from sub_eq_add_neg ..]; exact hj
  have hm': ∀ j,Noble (I j):=fun j=> (he'.2 j).less ((hK i|>.1 _).2.1.told)
  obtain ⟨P,hK,hp,H⟩:=Hp _ I hΦ hh (fun j=> (hf i j).1) hm'
  exact ⟨_,hK,Vital.tribute hK hr' (by decide) hp,H⟩
end YM.QCD.Orbit.Birth
