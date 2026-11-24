import YM.Iceberg.Aurora
import YM.Sprig.Echoes
import YM.Heron.Grail
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Iceberg
open Function Set Filter Analysis MeasureTheory Lattice
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair QCD QCD.Lat Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {ε β:ℝ}{φ:ℕ→ℕ}
variable (hp:C.Path β ε)(hP:P.System)(hHQ:K.Harmony P φ)(ht:Tendsto φ atTop atTop)(hf:Foil P K T)
variable (V:Face→K.W)(hv:Tense T V)(E:Canopy P φ K) (X:Lanterns T E)
open Lanterns Tawny Tawny.Cast Perla Carnal Drill
noncomputable def liftV (f:Face): K.level 8:=⟨V f,hv.lv f⟩
noncomputable def airs (k:ℕ)(p:Face): Free.Symbol 8:= (X.frame k 8).symm (liftV V hv p)
local notation "Rx" => RawTensor 1 8
variable (k d:ℕ)
set_option quotPrecheck false
local notation "Sx"=> airs V hv E X k
local notation "U"=> X.base 8
local notation "B"=> (X.base 8).liftS
noncomputable def patrolS :Rx:=by
   let F:= B ∘ Sx; let W:= X.frame k 8; have ha:= X.leaders k 8
   have hJ(f:Face):B (projection (F f))=F f:= congr_arg B ((X.base 8).right _)
   have hs(f:Face): (W (projection (F f))).val = V f:=by rw[show projection (F f)= Sx f from (X.base 8).right _,airs]; simp[W,liftV] -- simplify
   have ht(s:Face)(t:Label 8)(c:ℂ)(he:(W (projection t)).val=c • V s): B (projection t)=c • F s:=by
        rw [←hs s] at he; have h: projection t=c • (projection (F s)):= W.injective (by rw[map_smul]; exact Subtype.ext he); rw[h,map_smul,hJ]
   refine stoke F 1 (fun i j=>?_) (fun s w hw i j=>?_) ?_ -- stoke fun s w hw i j
   · let v:= F (i,j); have he: P.sym.charge 8 v=v:=by
                                  rw [show P.sym.charge 8 v=B (projection (P.sym.charge 8 v)) from (by unfold v; nth_rw 1 [← hJ (i,j)]; exact ((X.base 8).aligned.charge v).symm),ht (i,j) _ 1,one_smul]; rw[one_smul,show W= X.frame k 8 from rfl,← ha.jumps v]; exact Eq.trans (congr_arg T.charge (hs _)) (hv.charge _)
     refine ⟨⟨?_,fun u=>?_⟩,(P.sym.chargeActs _ v).symm.trans (congr_arg Subtype.val he)⟩
     · have hP:= ht (i,j) (P.sym.parity 8 v) 1 (Eq.trans (ha.spins v).symm (Eq.trans (congr_arg T.parity (hs _)) ((hv.parity _).trans (one_smul ..).symm)))
       rw[one_smul] at hP; exact (P.sym.parityActs _ v).symm.trans (congr_arg Subtype.val (show P.sym.parity 8 v=v from (Eq.trans (congr_arg (P.sym.parity 8) (hJ _).symm) (((X.base 8).aligned.parity v).symm.trans hP))))
     have hP:= ht (i,j) (P.sym.flavor 8 u v) 1 (Eq.trans (ha.turns v u).symm (Eq.trans (congr_arg (T.flavor u) (hs _)) ((hv.flux u _).trans (one_smul ..).symm)))
     rw[one_smul] at hP; exact (P.sym.flavorActs _ u v).symm.trans (congr_arg Subtype.val (show P.sym.flavor 8 u v=v from (Eq.trans (congr_arg (P.sym.flavor 8 u) (hJ _).symm) (((X.base 8).aligned.flavor v u).symm.trans hP))))
   · let v:=F (i,j); let p:=(s.perm i,s.perm j); let c:ℂ:=↑(signT s i*signT s j); have hP:= ht p (P.sym.pin 8 w v) c (Eq.trans (ha.rotates v w s hw).symm (Eq.trans (congr_arg (T.spin w) (hs _)) (hv.geo w s hw i j)))
     rw [←Complex.ofReal_mul]; exact (P.sym.pinActs _ w v).symm.trans (congr_arg Subtype.val (Eq.trans (congr_arg (P.sym.pin 8 w) (hJ _).symm) (((X.base 8).aligned.pin v w s hw).symm.trans hP)))
   intro i j; rw[one_smul]; apply congr_arg B; apply congr_arg (W.symm); exact Subtype.ext (hv.sym j i)
#check patrolS
lemma patio (i:Face): (patrolS V hv E X k).val i= (X.base 8).liftS (airs V hv E X k i):=rfl -- implicit parameters check
lemma petrol (i:Face): projection ((patrolS V hv E X k).val i)= airs V hv E X k i :=by rw[patio,(X.base 8).right]
-- give Symbol norm for pointwise. scoped. Need ℂ as field.
private local instance (d:ℕ):Module.Free ℂ (Free.Symbol d):=Module.Free.of_divisionRing ℂ (Free.Symbol d)
noncomputable def gates (d:ℕ):= (Module.finBasis ℂ (Free.Symbol d)).equivFun
noncomputable scoped instance sealF (d:ℕ): NormedAddCommGroup (Free.Symbol d):= NormedAddCommGroup.induced _ _ _ (gates d).injective
noncomputable scoped instance adL(d:ℕ):NormedSpace ℂ (Free.Symbol d):= .induced _ _ _ (gates d)
noncomputable scoped instance fitC(d:ℕ): CompleteSpace (Free.Symbol d) := FiniteDimensional.complete ℂ _
local notation "FV"=> Face→ Free.Symbol 8
noncomputable def paceG :FV:= (((E.B k).r:ℂ)^4) • Sx
noncomputable def peakΩ := ‖paceG V hv E X k‖
variable (A:Persona T V)
lemma viable : 0<peakΩ V A.tense E X k:=by
    unfold peakΩ paceG; rw[norm_pos_iff]; intro h; let v:= A.tense; have hh: airs V A.tense E X k=0:= (smul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by exact_mod_cast (E.B k).realH.ne'))
    apply A.non 0; rw[zero_smul]; funext i; have h:= congr_fun hh i; let F:= X.frame k 8; exact congr_arg Subtype.val (F.symm.injective (Eq.trans h (F.symm.map_zero).symm) : liftV V v i=0)
noncomputable def aceG (v: Tense T V):FV:= (↑(peakΩ V v E X k)⁻¹:ℂ) • paceG V v E X k
-- signature
#check aceG
lemma lives :∃ (f:ℕ→ℕ)(v:FV), StrictMono f ∧ ‖v‖=1∧ Tendsto (fun i:ℕ=>aceG V E X (f i) A.tense) atTop (𝓝 v):=by
    let F(k):=aceG V E X k A.tense
    let S:= Metric.sphere (0:FV) 1; haveI :ProperSpace (FV):= FiniteDimensional.proper ℂ _
    have h(k:ℕ):F k∈S:=by rw [Metric.mem_sphere,dist_zero_right]; have h:=viable V E X k A; rw [show F k=aceG V E X k A.tense from rfl,aceG,norm_smul]; -- inv cast syntax checks
                            push_cast; rw[norm_inv,Complex.norm_real,Real.norm_of_nonneg h.le]; exact inv_mul_cancel₀ h.ne'
    obtain ⟨v,hv,f,hf,hX⟩:=(isCompact_sphere (0:FV) 1).tendsto_subseq h
    exact ⟨f,v,hf,(dist_zero_right v) ▸ (Metric.mem_sphere.mp hv),hX⟩
end YM.Iceberg
#print axioms YM.Iceberg.lives
#print axioms YM.Iceberg.patio
