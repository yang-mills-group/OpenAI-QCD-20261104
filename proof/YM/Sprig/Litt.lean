import YM.Sprig.Faun
/-! Point rotations.Dim.Cost real.Transfer to normalized cofinal contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
variable {C:Sequence} {D d n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
namespace Compass
variable (A:Compass C D)
variable (Z:ℕ→ ∀ d,Label d→ₗ[ℂ]Label d)(φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d) {β e:ℝ}(ht:C.Path β e)
set_option quotPrecheck false
variable (h:Tendsto φ atTop atTop)(hg: grace (D:=D) Z φ V)(hp:∀ᶠ i in atTop,Plot P A i (Z i))(hA: Known A) (Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
local notation "S"=>Q.total
-- ledger.Tick.d.Physical equality.
noncomputable def choiceT (p:Label d):Q.W:= Q.focus none d (V d p)
noncomputable abbrev learned(X:Fin n→ Glyph D)(y:Fin n→ E4):ℂ:= Q.total n (A.r • points y) (fun i=>choiceT V Q (X i).material)
variable (X:Fin n→ Glyph D)(y:Fin n → E4)(hu:∀ i,X i∈A.Ω)(hZ:∀ i,(X i).material≠0)(hw:n≤ A.K)
set_option quotPrecheck false
noncomputable def readings (f:ℕ→Fin n→ Cover)(i:ℕ):= (C.A i).regulator.average (List.ofFn (treeX P i (Z i) X (f i))).prod
lemma token_τ (k:ℕ)(x:Strings n):pollF C n k x=A.r • points (A.qR (C.N k) ∘ x):=by
    apply PiLp.ext; intro j; apply PiLp.ext; intro a; change C.S.spacing (C.N k)*(x j a)=A.r*((C.S.spacing (C.N k)/A.r)*(x j a)); have h:=A.realH; field_simp
include h hQ hg
lemma flight (f:ℕ→ Fin n→ Cover)(hs:Injective y)(hv:Tendsto (fun i=> (A.qR (C.N (φ i))) ∘ (f (φ i))) atTop (𝓝 y)) :Tendsto (readings P Z X f ∘φ) atTop (𝓝 (learned A V Q X y)):=by
     let a:= A.r; let x:=points y; let W:=Q.total n; let p(i:Fin n):= (X i).width; let F₁(i:ℕ)(j:Fin n):Label (p j):= Z i (p j) (X j).material; let F₂(j):Label (p j):= V (p j) (X j).material
     have hy: A.r • x∈conf n:=by intro i j he; change a • y i=a • y j at he; exact hs (smul_right_injective E4 A.realH.ne' he)
     have hp:Tendsto (fun i=> (pollF C n (φ i) (f (φ i)))) atTop (𝓝 (a • x)):=by
             have hx:Tendsto (fun i=> A.r • points (A.qR (C.N (φ i)) ∘ (f (φ i)))) atTop (𝓝 (a • x)):= (((show Continuous (points (n:=n)) from by unfold points; fun_prop).tendsto _).comp hv).const_smul a
             exact hx.congr fun i=>(A.token_τ (φ i) (f (φ i))).symm
     have he:=hQ.exposed p (fun _=>none) F₂ (F₁ ∘φ) (tendsto_pi_nhds.mpr fun j=>hg (p j) (X j).raised _) _ hy
     have hT:= he.comp (YM.Fir.NoteF.ride (v:=fun i=>pollF C n (φ i)) _ _ tendsto_id hp)
     change Tendsto _ atTop _
     exact hT
variable (x: Fin n→ Cover)
include hp ht hA hu hZ hw
lemma stalked(hf:A.qR A.ℓ ∘x∈ flats (Fin n) (2*A.e) (A.v/2)):‖learned A V Q X (A.qR A.ℓ ∘ x)- candle X (A.qR A.ℓ ∘ x)‖ ≤ A.bid:=by
     let y:= A.qR A.ℓ ∘ x
     let f (i:ℕ):Fin n→ Cover:= A.hike i ∘ x
     have he:∀ᶠ i in atTop, A.qR (C.N i) ∘ f i=y:=by filter_upwards [ht.uv.tendsto_atTop.eventually_ge_atTop A.ℓ] with i hi; exact funext fun j=> (hA.Γ.joins (x j) hi).symm
     have hT:= flight P A Z φ V h hg Q hQ X y f (noCol _ _ y hf (mul_pos (by norm_num) hA.live)) (tendsto_const_nhds.congr' ((h.eventually he).mono fun x hx=> hx.symm)); exact le_of_tendsto ((hT.sub_const _).norm) (((hp).mono (fun i hi=>hi.here n X hu hZ hw x hf))|> h.eventually)
variable (f:ℕ→ Fin n→ Cover)
-- transport normalized coords directly.B fuse.
lemma choicesP (y:E4):∃ f:ℕ→ Cover,Tendsto (fun i=> A.qR (C.N i) (f i)) atTop (𝓝 y):=by
    let r(i):= C.S.spacing (C.N i); let z:= A.r • y; let a(i):=r i /A.r; let f(i):= bead (a i) y; have hx:Tendsto a atTop (𝓝 0):= by have h : Tendsto r atTop (𝓝 0):= tendsto_nhds_of_tendsto_nhdsWithin ht.physical; simpa [a] using (h.div_const A.r)
    have hh:Tendsto (fun i=>2*a i) atTop (𝓝 0):=by simpa only[mul_zero] using (hx.const_mul 2)
    refine ⟨f,Metric.tendsto_nhds.mpr fun ε he=>?_⟩; exact (hh.eventually_lt_const he).mono fun i hi=> lt_of_le_of_lt (smoothV (k:=a i) (div_pos (space0 _ _) A.realH) y) hi -- y arg remove
-- growth cap all.Cube. Distinct shifts already allowed. layouts kept.
set_option maxHeartbeats 800000
lemma hugs(k:ℕ)(y:Fin n→ Cover)(ht':Plot P A k (Z k))(hp':A.qR (C.N k) ∘ y ∈ flats (Fin n) (2*A.e) (A.v/2)): ‖readings P Z X (fun _=>y) k‖ ≤ A.dB^n:=by
    obtain ⟨a,p,he,hp,hK,h,hR⟩:= ht'.segment n X hu hZ hw y hp'; let T':= Column.sky C.S (C.R k) A.pB (C.N k) he (evenW _ _ hp _) a
    have hy(j:Fin n):Gold (C.A k).regulator T' (p j) (treeX P k (Z k) X y j) A.dB:= (coin (hR j).1 ⟨_,(hR j).2.1⟩).mono (hR j).2.2
    have he:= Gold.value (T:=T') (R:=(C.A k).regulator) p hK _ (fun _=> A.dB) hy rfl rfl ((ht.normalized k).beta_pos le_rfl|>.le) (Hub.sideW ht k _) ((Massive.Needle.engaged ht k)) -- namespace
    simpa only [readings, Finset.prod_const,Finset.card_univ,Fintype.card_fin] using he
lemma copper(hx:y∈ flats (Fin n) (3*A.e) (A.v/4)):‖learned A V Q X y‖ ≤ A.dB^n:=by
    choose g hg' using fun j:Fin n=> choicesP P A Z φ V ht h hg hp hA Q hQ X hu hZ hw (y j)
    let f(i)(j):= g j i
    let F(i):= A.qR (C.N i)∘ f i
    have hp': Tendsto F atTop (𝓝 y):=tendsto_pi_nhds.mpr hg'
    have hz:∀ᶠ i in atTop, F i ∈flats (Fin n) (2*A.e) (A.v/2):=by
            have ht : Tendsto (fun i=>‖F i-y‖) atTop (𝓝 0):=by simpa using (hp'.sub_const y).norm
            filter_upwards [ht.eventually_lt_const (div_pos hA.live (by norm_num:(0:ℝ)<3)),ht.eventually_lt_const (div_pos hA.space (by norm_num:(0:ℝ)<10))] with i hi hp; exact puff _ _ y hx (F i) _ _ _ le_rfl (by linarith only[hi,hA.live]) (by linarith only [hp,hA.space])
    have hT:= (flight P A Z φ V h hg Q hQ X y f (noCol _ _ _ hx (by linarith only[hA.live])) (hp'.comp h)).norm
    exact le_of_tendsto hT (show ∀ᶠ i in atTop, ‖readings P Z X f (φ i)‖ ≤ A.dB^n from h.eventually ((hp.and hz).mono fun i hi=> hugs P A Z φ V ht h hg hp hA Q hQ X hu hZ hw i (f i) hi.1 hi.2))
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.flight
#print axioms YM.Intag.Sprig.Compass.copper
#print axioms YM.Intag.Sprig.Compass.stalked
