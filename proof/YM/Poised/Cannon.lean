import YM.Poised.Sheets
import YM.Poised.Drought
import YM.Poised.Looms
import YM.Poised.Transits
import YM.Poised.Pacific
import YM.Poised.Fountain
import YM.Poised.Street
import YM.QCD.Fawn.Price
/-!
# Charter interior, picks real Crown.
Shrink discharged D.ε at furnishing before actual x height. Allows full-rank path cost with constant output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open QCD QCD.Lat QCD.Kit QCD.Grass QCD.Brick QCD.Cove QCD.Stew ConnectedActivityE6.Blaze Push.Uniform UV Cylinder SourceRead
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {B :Type}[Fintype B] {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio}
    {P R : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v s u u₁ u₂: ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j q₀ : ℕ} {D : Slab su c l} {q : Chi} {d : ℝ} {V' : Config su f → Lat.Fields f 6}
namespace Fountain
open Pipes
local notation "Y'"=> Fields f 6 -- remove amb
variable (a:Museum F x A X Y I)[Fintype I] {C: Libretto su n}{E: Heir.Record}
variable (hp:Plays C E P R Pt T x) (b:Cover) (hw:wrap f b∈X) (hg :Canvas P (S.ratio.parent (wrap f b)) (reach x) V g n C.C)
variable (hO:Short S R X)(hn:2≤n)(hV: Healthy P.threshold Y V) (U:Grid f)(z: Prices su I)(hu:0≤u) (hv:u*‖tape z‖≤ E.ε*R.threshold)(hl:l≤n) (hD:∀ i,P.dirBound (S.ratio.parent (wrap f b)) (D i))
set_option quotPrecheck false
local notation "O"=> S.ratio.parent (wrap f b)
local notation "X₀"=> enters V (S.ratio.parent (wrap f b)) (reach x) g D (a.extra g u z)
local notation "Z₀"=> launch V (S.ratio.parent (wrap f b)) (reach x) g D
local notation "V₀"=> Heir.loom P (reach x) C.C
local notation "b'"=> Kit.slope S.patch.L
variable {p p₀ :ℕ}{I₀ I₂ χw R₁ :ℝ}
open PhysicalNext.Repeat Cub
-- ,g=1 even no Short; agreement common chart at identity.
variable [DecidableEq I](α: Directions su c)
local notation "F⚬"=> (1:Frame c)
local notation "V⚬"=> (1:Grid c)
local notation "qe"=> a.extra F⚬ u z
open MultiNext.SignedSource MultiNext.SignedSource.Lyre
variable (N Yp:ℝ)(hA:‖α‖ ≤ N*loom P (reach x) C.C) (hN:1 ≤ N)
local notation "An"=> Heir.loom P (reach x) C.C
local notation "D0"=> fun s:ℝ=> (rod α s,a.extra (1:Frame c) u z)
local notation "v0"=> route T ∘ rod α
local notation "m0"=> u*‖tape z‖
local notation "ψ₁"=> ((E).Q)
variable (i:ℕ) (w:B→ℝ)(U':VectorD (Site f) B)(fw A₀:ℝ) (hq:SeatD (purseX (wrap f b) i fw) w U' Yp) (hYp:1 ≤Yp)
local notation "Y₂"=> purseX (wrap f b) i fw
variable (ht:∀ i,w i>0)(hf:fw>0)(hκ:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→ Through n (yaw i j) x A₀)(hM:C.M*(N*loom P (reach x) C.C) ≤1)
variable (W:ℝ) (hW:0 ≤ W) (hqW: clinicFee n E.Q*loom P (reach x) C.C ^2 * N^n + u*‖tape z‖≤ W*R.threshold) (hΨ: (1+patterns n)*(A₀*(C.M*(N*loom P (reach x) C.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W)
-- comparator.Quasi.P. `mouth` constant needs path.S seat at **Yp constant**! H 0=0? φ(y=0)=0 so y.2−...=0. use exact.
variable (f':Grid f→Lat.Fields f 6)(nf:ℕ)
set_option quotPrecheck false
local notation "s0"=> quakes T α U'
local notation "s'"=> shiver T F x k α qe U'
local notation "Xt"=> (framesF w∘lotsF f')
variable (hG : ∀ k U,slots 6 k (f' (Lattice.gauge k U))=f' U) (heV:Ease.Charm R X f') (hS:∀ V,f' V∈ Creek.region (limits X)) (hB:∀ V,f' V ∈ layer (Faces (Site f)) nf)
variable (hh:R.supBounds (wrap f b) X (framesF (purseX (wrap f b) i fw)∘f') τ)(Vb:Hera.Rights su n)
variable (hhA:Sized Yp (route T α) R (wrap f b))(hLi:∀ i,Mom.needed X i→ width R (wrap f b) i ≤1)
local notation "Kⁱ"=>framesF w ∘ cherub T U' f'
variable (L:Alg B→L[ℝ]ℝ)(hlL:‖L‖ ≤1) (χ:Chi)
open AnalyticBridge.LocalGaussian.Moments Heir.Lute Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score AnalyticBridge.LocalGaussianLaws Heir.Carillon
-- first.Clue input chart actual.
local notation "Rz"=>Pipes.mouth (1+n+Yp) Vb n nf
local notation "θ!"=> guard χ su I u (E.ε*R.threshold)
local notation "gq"=> fun A:Grid f=> framesF w (changeVars U' (f' A))
local notation "Vq"=> fun V:Grid c=>gq (a.received k T q d u V U z)
local notation "ve"=> L ∘ (gq)
-- charts vector from postcomp coordinates
include hp hG heV hn hu hv hw
lemma scion : Push.Local.Chart n (Vq) 1:=by
    let M:=Module.finBasis ℝ (Alg B); let l(i):=(M.coord i).toContinuousLinearMap; let X:= Vq ∘ increment (1:Grid c)
    have hc(i):ContDiffAt ℝ n (l i ∘ X) 0:=by
       have hp':=(atReception (g:=1) (V:=1) (q:=q) (d:=d) (k:=k) a hp b hw (Cub.posed C.Z hp.rehearsed.wire) hn (one_healthy _ _ P.threshold_pos.le) U z hu hv w U' f' hG heV (l i))
       simp only at hp'; simp_rw [show ∀ U: Grid f,Lattice.gauge ((1:Frame c)∘ S.ratio.parent) U=U from fun U=> by funext j; simp [Lattice.gauge]] at hp' -- rw only one?
       exact ContDiffAt.comp (f:=fun p:Directions su c=> (p,z)) 0 hp' (contDiffAt_id.prodMk contDiffAt_const)
    change ContDiffAt ℝ n X 0; rw [show X=fun p=>∑ i, l i (X p) • M i from funext fun p=>(M.sum_repr _).symm]; exact ContDiffAt.sum (fun i _=> (hc i).smul contDiffAt_const)
omit hv
variable (hd:P.dirBound (S.ratio.parent (wrap f b)) α) {rm m₃ :ℕ}
local notation "αΓ"=> fun v=> v=α
variable (hW': 0<W)(h0:W≤1) (hts:Walled S X Y x rm)
-- in cost W normalized z.Seat pledge from opal * etc.
local notation "Oz"=> (opal C E P R S.patch.L X rm x u)
local notation "vt"=> R.threshold*Carillon.pitch n _ E.Z (Heir.scope R X rm x) P.power z
local notation "H"=>powers z ^ 2
local notation "γ"=> Carillon.speed n E.Z R.threshold P.power (Heir.scope R X rm x) z
variable (hhOz: opal C E P R S.patch.L X rm x u *N^n ≤ W)
local notation "T'"=> patterns n*(1+(2:ℝ)^n)*(Yp+1)^n * Rz
local notation "Tq"=> patterns n*(Yp^n*Rz*τ)
local notation "D!"=> T' * (W*H^(n+1))*τ
include hW' hN hhOz hp hM hf ht hlL hA hq hκ hΨ hYp hhA hd hLi h0 hts χ hh hB Vb
omit hu
variable (huP:0<u)(hhx :m₃<n) -- name
include huP
lemma rich (hm:m₃<n): let A:= Complex.ofRealCLM ∘ L ∘ Kⁱ
    Band m₃ αΓ V⚬ (γ+1) (D! + (W*H)*Tq+(W*H)*Tq) ((a.concert T u q d k ve θ! U 1 z)-A):=by
    intro C'; have ht0:0≤ Rz:=by unfold Pipes.mouth; have h:=Vb.large; positivity
    have h00 :1≤ H := one_le_pow₀ (grows z)
    let f₀:= Kⁱ; let Lz:= Complex.ofRealCLM.comp L; let F₀ := θ!; let Ψ :Grid c→ℂ:= Lz∘(Vq); let p:= Oz; let S':=W*H; have hS : 0<S':=by unfold S'; positivity
    obtain ⟨hT,hX⟩:= sunny (S:=S) (C:=C) (X:=X) (P:=P) (B:=R) (x:=x) (r:=rm) χ huP z (D:=E)
    let Df0:=γ+1; let A0 := D!; let Z0:= Tq; have ht' := one_healthy (G:=su) Y _ P.threshold_pos.le; have hτ:=hh.1
    have hR : 0 ≤ An := by unfold Heir.loom; have h:=C.C_one; have ht:=P.threshold_pos; positivity
    have h : Oz ≤ W:= (le_mul_of_one_le_right (opal_nn _ _ _ _ _ _ _ _ _ huP.le) (one_le_pow₀ hN)).trans hhOz
    have he : 0 ≤ Z0:=by unfold Z0; positivity [patterns_nonneg n]; -- indentation
    have hv:0≤ A0:=by unfold A0; positivity [patterns_nonneg n]
    have ha {F: Grid c→ℂ}{j v:ℝ}(h:Band n (P.dirBound (S.ratio.parent (wrap f b))) V⚬ j v F): Band m₃ αΓ V⚬ j v F:=by
       have he := h.readable; have hk: ContDiffAt ℝ (m₃:WithTop ℕ∞) _ _:= he.germ.of_le (Nat.cast_le.mpr hm.le)
       exact ⟨into m₃ F hk,h.sane,h.nonneg,fun l hl hq=>h.caps _ (hl.trans (by omega)) (fun i hi=> (hq i hi).symm ▸ hd)⟩
    have hk:= hp.cantos (k:=k) a ht' hts hw; have hp':= ha (ivory hk R.threshold_pos.le R.threshold_le E.chimes z) -- :=
    have hs:= hk.sing R.threshold_pos.le R.threshold_le E.chimes z; have hV:0 ≤ vt := hp'.nonneg
    have hV₀ : vt ≤ W*H:=by
       have hr0:= Cub.tide (D:=E) (P:=P) (B:=R) a hts hw z (by omega:1 ≤ n); have hx: scratch (n:=n) su E P R S.patch.L X rm x ≤ W := by
          refine le_trans ?_ h; apply le_trans _ (show Lute.rust C E P R _ _ _ _ _ ≤ p from le_add_of_nonneg_right (by have hQ:= E.guards; unfold ζ; have hr:=R.threshold_pos; positivity)); unfold rust; exact le_add_of_nonneg_left (add_nonneg (segment_nn n X P R E.majorant C.matins) (tranche_nn _ _ (zero_le_one.trans E.majorant) huP.le R.threshold_pos.le))
       exact hr0.trans (mul_le_mul_of_nonneg_right hx (sq_nonneg _))
    have hs' : 1≤ Df0 :=le_add_of_nonneg_left hp'.sane
    have hL : ‖Lz‖ ≤ 1:=by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; change ‖(↑(L i):ℂ)‖ ≤ _; rw [Complex.norm_real]; exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hlL (norm_nonneg _))
    have hζ (l:List (Directions su c))(h:∀ i∈l,i=α): l= List.replicate l.length α:=by
       induction l with
       | nil=>rfl 
       | cons a l ih=>
           conv_lhs=> rw [h a (by simp),ih (fun i hi=> h i (List.mem_cons_of_mem _ hi))]
           simp [List.replicate_succ]

    have hf0:Push.Local.Chart n f₀ 1:= (framesF w).contDiff.contDiffAt.comp _ (nest (T:=T) U' f' heV hp.rehearsed.orders)
    have he' : Band m₃ αΓ V⚬ 1 Z0 C':=by
        have hG: Germ n C' V⚬:= Lz.contDiff.contDiffAt.comp _ hf0
        refine ⟨into _ _ (hG.prod hm.le),zero_le_one,he,fun l hl hq=>?_⟩; conv_lhs=> rw [hζ l hq]
        let n':=l.length; let p:=List.replicate n' α; change ‖leftDerivs (Lz ∘ f₀) p _‖≤ _; rw [one_pow,mul_one,Push.Local.left_linear _ _ hf0 (by simp [p,n',hl.trans hm.le])]
        exact (Lz.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (costume b α Yp i w U' fw (by assumption) hYp hf f' nf heV hB hh Vb hhA hLi hp.rehearsed.orders n' (hl.trans hm.le))) -- hq rename
    have hGv : ‖(θ!) z-1‖≤ W*H:= hT.trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))
    by_cases hy : z∈ tsupport (θ!)
    swap
    · have hq:= image_eq_zero_of_notMem_tsupport hy
      rw [show a.concert T u q d k ve (θ!) U 1 z=0 from funext (fun W=>by unfold Museum.concert; rw [hq]; simp),zero_sub]; have hΓ : Band m₃ αΓ V⚬ 1 Z0 (-C'):= by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using (he'.scale (-1))
      apply band_rise hΓ _ hs'; rw [hq,zero_sub,norm_neg,norm_one] at hGv; exact (le_mul_of_one_le_left he hGv).trans (le_add_of_nonneg_left (add_nonneg hv (mul_nonneg hS.le he)))
    have hθ:= guard_silent χ huP (mul_pos E.guards R.threshold_pos) (n:=n) (I:=I) (G:=su); have hp0: Push.Local.Chart n Vq 1:= scion a hp b hw hn U z huP.le (hθ.stay z hy) w U' f' hG heV
    have hqW': clinicFee n E.Q*(Heir.loom P (Heir.reach x) C.C)^2 *N^n+m0 ≤ S'*R.threshold:=by
       have hpZ := mul_le_mul_of_nonneg_right hX (show 0 ≤ N^n by positivity)
       have hh : paint C E P R x m0*N^n ≤ W*H:=hpZ.trans ((le_of_eq (mul_right_comm ..)).trans (mul_le_mul_of_nonneg_right hhOz (sq_nonneg _)))
       unfold Cub.paint at hh; rw [div_mul_eq_mul_div] at hh; have h:= (div_le_iff₀ R.threshold_pos).1 hh; refine le_trans ?_ h; rw [add_mul]; exact add_le_add le_rfl ( le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN))
    have hb : Band m₃ αΓ V⚬ 1 A0 (Ψ-C'):=by
       have hx:Germ n Ψ V⚬:= Lz.contDiff.contDiffAt.comp _ hp0; have hψ:=into m₃ Ψ (hx.prod hm.le)
       refine ⟨into m₃ _ ((hψ.germ
         ).sub he'.readable.germ), zero_le_one,hv, fun l hl hU=>?_⟩
       rw [Cub.redacted hψ he'.readable hl]; conv_lhs=> rw [hζ l hU]
       let p:=List.replicate l.length α; have hz:p.length ≤ n:=by simp [p,hl.trans hm.le]
       change ‖leftDerivs (Lz ∘ (Vq)) p _- leftDerivs (Lz∘ Kⁱ) p _‖≤ _; rw [Push.Local.left_linear _ _ hp0 hz,Push.Local.left_linear _ _ hf0 hz, ← map_sub,one_pow,mul_one]
       apply (Lz.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans _)
       have h:= risk (q:=q) (d:=d) (k:=k) a hp b hn U z huP.le (hθ.stay z hy) α N Yp hA hN i w U' fw A₀ hq hYp ht hf hκ hM S' hqW' (hΨ.trans (le_mul_of_one_le_right hW'.le h00)) f' nf hG heV hB hh Vb hhA hLi hS l.length (lt_of_le_of_lt hl hm)
       apply h.trans; have hr:Yp+W*H≤(Yp+1)*H:=by rw [add_mul,one_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) h00) (mul_le_of_le_one_left (sq_nonneg _) (by assumption))
       unfold A0; unfold S'; calc
          _≤ patterns n*((1+(2:ℝ)^n)*((W*H)*((Yp+1)*H)^n*Rz*τ)):=by have h:=patterns_nonneg n; gcongr
          _ = _:=by rw [mul_pow,pow_succ]; ring -- rw mul_pow ambiguity
    let w':= (F₀ z:ℂ); have hk:‖w'‖≤1 := (Complex.norm_real _).trans_le (hθ.little z)
    let gZ(y:Grid c):ℂ:= Carillon.vary V⚬ (a.twilight k T) z y
    have hΩ: Band m₃ αΓ V⚬ Df0 A0 (w' • (gZ*(Ψ-C'))):= band_rise (((ha hs).multiply hb).scale w') (by rw [one_mul]; exact mul_le_of_le_one_left hv hk) le_rfl
    have hβ: Band m₃ αΓ V⚬ Df0 ((W*H)*Tq) (w' • ((gZ-(fun _=> (1:ℂ)))*C')):= band_rise ((hp'.multiply he').scale w') ((mul_le_of_le_one_left (mul_nonneg hV he) hk).trans (mul_le_mul_of_nonneg_right hV₀ he)) le_rfl
    have hP0 := band_plus (band_plus hΩ hβ) (band_rise (he'.scale (w'-1)) (c':= S'*Z0) ?_ hs') -- `b` name
    apply Eq.mp ?_ hP0; swap; · rw [show w'-1=((F₀ z-1:ℝ):ℂ) from by simp [w'], Complex.norm_real]; exact mul_le_mul_of_nonneg_right hGv he
    congr 1; ext1 s; simp only [w',F₀,C',Ψ,Lz,gZ,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul, Museum.concert]; simp; ring -- simp ring
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.rich
