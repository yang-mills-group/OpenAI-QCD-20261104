import YM.QCD.Sparks.Cavities

/-! # translation boosts agree up to sign; recover every source -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve RG Tavern
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {N n:Side}{b k:ℕ}{r C:ℝ}{I:Type}{F:trackG n}

lemma prism {P:I→Bloom k}(h:Fractal P r C)(x: Lat.Frame n) (U: Grid n): dust P n (Lattice.gauge x U)= aura (siteRot x) (dust P n U):=by
  unfold dust; simp_rw [fun i=>(P i).toneRotation U (0:Site n) 0 x (h.sect i)] -- name
  unfold aura; rw [Summable.tsum_mul_right, (h.tonics ..).of_norm.tsum_mul_left]; exact (h.tonics ..).of_norm.mul_left _
lemma raw {P:I→Bloom k}(h:Fractal P r C)(U:Grid n)(L:Window n N b){d}(hp:Quaint L d): dust P N (L.links U)*stream L d= stream L d*dust P n U:=by
  let M : Sheet N→L[ℂ] Rail N n:=LinearMap.toContinuousLinearMap { toFun:=fun i=>i*stream L d,map_add':=fun _ _=> Matrix.add_mul ..,map_smul':=fun _ _=>Matrix.smul_mul .. }
  let B : Sheet n→L[ℂ] Rail N n:=LinearMap.toContinuousLinearMap { toFun:=fun i=>stream L d*i,map_add':=fun _ _=> Matrix.mul_add ..,map_smul':=fun _ _=> Matrix.mul_smul .. }
  change M (dust P N (L.links U))= B (dust P n U); unfold dust; rw [M.map_tsum (h.tonics ..).of_norm,B.map_tsum (h.tonics ..).of_norm]; exact tsum_congr fun i=> pint hp ..
set_option maxHeartbeats 30000 in
lemma quota {P:I→Bloom k}(h:Fractal P r C)(hh:0<r):Priest (metastage P n):=by
  refine ⟨serenity h hh,?_,fun u=> ?_, ?_⟩
  · intro x; obtain ⟨d,hp⟩:=twinkle (parallel x) (k:=1) (mul_one _).symm odd_one; refine ⟨d,hp, Eventually.of_forall (fun i=> ?_)⟩; unfold metastage; rw [input_run,pull_one]; exact raw h (input su n i) (parallel x) hp
  · refine Eventually.of_forall (fun z=>?_); unfold metastage; rw [← stain_cons, prism h]
  filter_upwards [moveField_germ (G:=su ) (m:=n)] with i hi; unfold metastage; rw [hi]; exact prism h (switchSite i.1) (input su n i.2)
lemma grove {P:I→Bloom k}(h:Fractal P r C)(hh:0<r)(S: SparkMesh):Clan S (fun i=> metastage P _):=by
  refine ⟨fun i=>quota h hh,fun i j e=>?_⟩; obtain ⟨d,h⟩:= twinkle (S.vista i j e) (S.factor i j e) (S.parity i j e); rename_i hu
  refine ⟨d,h,Eventually.of_forall (fun x=>?_)⟩; unfold metastage; rw [expandsC]; exact raw hu _ _ h
lemma check_sign {U:Window n N k} (d a : Site N→ℂ) (h:Quaint U d)(he:Quaint U a): ∃ c:ℂ,c≠0 ∧∀ x,a x=c*d x :=by
  have hh : d 0 ≠ 0:= by rcases h.sign 0 with h|h <;> simp [h]
  have hv : a 0≠0 := by rcases he.sign 0 with h|h <;> simp [h]
  refine ⟨a 0/d 0,div_ne_zero hv hh,fun x=>?_⟩; nth_rw 1 [factor_period he 0 x]; rw [factor_period h 0 x]; field_simp -- inspect
lemma ledger {U:Window n N k}{d a : Site N→ℂ} (h:Quaint U d)(he:Quaint U a)(B:Sheet N)(F:Sheet n)(hk:B*stream U d=stream U d*F) : B*stream U a=stream U a *F := by
  obtain ⟨c,_,H⟩:=check_sign _ _ h he
  have hh: stream U a=c • stream U d:=by ext i j; unfold stream; simp only [Matrix.smul_apply,Matrix.of_apply, H]; split <;> simp
  rw [hh, Matrix.mul_smul, Matrix.smul_mul,hk]
lemma Priest.day (h:Priest F)(x:Site n)(d)(he:Quaint (parallel x) d):∀ᶠ U in 𝓝 0,F (spaceShift x U)*stream (parallel x) d= stream (parallel x) d*F U:=by obtain ⟨y,hy,h⟩:=h.covenant x; exact h.mono fun _ hw=>ledger hy he _ _ hw
lemma Priest.less {G: trackG n}(h:Priest F)(p:Priest G): Priest (F-G):=by
  refine ⟨h.ready.sub p.ready,?_,fun u=> ?_, ?_⟩
  · intro x; obtain ⟨d,hp,H⟩:= h.covenant x; refine ⟨d,hp,?_⟩
    filter_upwards [H,p.day x d hp] with i hi he; simp only [Pi.sub_apply,Matrix.sub_mul,Matrix.mul_sub,hi,he]
  · filter_upwards [h.color u,p.color u] with i hi he; simp only [Pi.sub_apply,hi,he,aura_sub]
  filter_upwards [h.forced,p.forced] with i hi he; simp only [Pi.sub_apply,hi,he,aura_sub]
lemma Clan.less {S:SparkMesh} {F G:S.Field}(h:Clan S F)(he:Clan S G): Clan S (F-G):=by
  refine ⟨fun i=> (h.way i).less (he.way i),fun i j H=>?_⟩
  obtain ⟨d,hp,hq⟩:= h.order i j H; obtain ⟨q,hr,hs⟩:= he.order i j H
  refine ⟨d,hp,?_⟩; filter_upwards [hq,hs] with x hx hy; have hu:=ledger hr hp _ _ hy; simp only [Pi.sub_apply,Matrix.sub_mul,Matrix.mul_sub,hx,hu]

lemma acrossTown (h: Priest F)(x : Cnr n)(k:ℕ)(hv:∀ x y,Run.cell (surge F (fun _:Fin k=> x)) 0 y=0): surge F (fun _:Fin k=> x)=0:=by
  ext ⟨i,a⟩ ⟨j,b⟩; obtain ⟨d,hq,H⟩ := h.covenant i
  let p:= parallel i
  have hm:= pinhead h.ready h.ready (fun _:Fin k=>x) H
  have hh:= velvet p d _ _ hm 0 j; rw [show p.cut 0=i from zero_add _,Finset.sum_eq_zero (fun v _=> ?_)] at hh; swap
  · change (if _ then _ else _)= _; split
    · erw [show Run.cell (surge F _) (0:Site n) v=_ from (show Run.cell (surge F (fun _:Fin k=>spaceShift i x)) 0 v=0 from hv ..),smul_zero]
    rfl
  rcases hq.sign 0 with he|he
  · rw [he,one_smul] at hh; exact Matrix.ext_iff.mpr hh a b
  rw [he,neg_smul,one_smul,neg_eq_zero] at hh; exact Matrix.ext_iff.mpr hh a b
end YM.QCD.Sparks
