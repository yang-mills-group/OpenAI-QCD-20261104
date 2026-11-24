import YM.Mistral.Banks
import YM.Mistral.Wock
import YM.Needle.Pond
import YM.Rill.Vault
/- escaping offset stencils: rank using charged top histories rather than proximity through seams.M.N -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
variable {d:ℕ}{s:RawSym}(H:Vale.Laurel d)(K:Landing s H)
open Needle Needle.GaugeP Hub YM.Fir YM.Massive.Fir
variable {C:Sequence}{P:Calibration C}(B:Invest P d)(Hp:Rack B) (Z:Laurel d)(Y:Landing P.sym Z)(F:GaugeP P Z Y)(G:Capital P d 1)
variable (W: Choir) {φ:ℕ→ℕ}(hp:Tendsto φ atTop atTop)(hW:W.Harmony P φ)
variable {β e:ℝ}(hC:C.Path β e)(hr:Sway C.S)
variable (f g:ℕ→ Label d)
-- Preserve payment bank.F.E.Ph.Ph shadow plus.T union. Precision via creditW.
local notation "Fx" i:arg=> stem P d i (f i)
local notation "ß" i:arg=> F.ridge i ((tip F B i) (f i))
set_option quotPrecheck false
include F hC hr G
lemma dimWave (E:ℝ)(he:0≤E)(hF:∀ᶠ i in atTop, ‖tipEnd F B i (f i)‖ ≤ E*B.scale i):DimP C (fun i=> stem P d i (f i)-stem P d i (F.ridge i ((tip F B i) (f i)))):=by
      filter_upwards [Investment.creditW B] with j hv; obtain ⟨p,hP,h⟩:=hv; refine ⟨fun i=>E*(B.scale i*p i), (show _ from (by simpa only [mul_zero] using hP.const_mul E)),?_⟩; filter_upwards [h,hF, slices hC F hr G B] with i hi hew hJ
      have ht : f i-ß i= Investment.face B i (tipEnd F B i (f i)):=sub_eq_of_eq_add (?_); swap; · exact (hJ _).symm.trans (add_comm ..)
      refine ⟨mul_nonneg he (mul_nonneg (B.pos _) hi.1),?_⟩; change GreenP C i j _ _; rw [← map_sub,ht]; exact GreenP.mono (hi.2 _) ((mul_le_mul_of_nonneg_right hew hi.1).trans_eq (by ring))
omit F G
-- physical certificate using any f_N, converted to standard read, leak DimP.Budget lemma.Actual
noncomputable abbrev Tracked (P:Calibration C) (d:ℕ) (k:ℕ→Label d) (φ:ℕ→ℕ)(x:Label d):Prop:=∃ g:ℕ→Label d,(∃ A:ℝ,0 ≤ A∧∀ᶠ i in atTop,‖g i‖≤ A) ∧ Tendsto (g ∘φ) atTop (𝓝 x) ∧ DimP C (fun i=> stem P d i (k i)-stem P d i (g i))
omit hC hr
lemma tracksZ (x:Label d)(hx:Tendsto (f ∘φ) atTop (𝓝 x))(h:∃ A:ℝ,0 ≤A ∧∀ᶠ i in atTop, ‖f i‖≤ A):Tracked P d f φ x:=by refine ⟨f,h,hx,?_⟩; filter_upwards with j; refine ⟨0,tendsto_const_nhds,?_⟩; filter_upwards with i; change 0 ≤ (0:ℝ)∧ _; simp only [sub_self]; exact ⟨le_rfl, GreenP.zero⟩
lemma tracksT {d:ℕ}(z:ℕ→Label d)(p:Label d)(H:Tracked P d z φ p)(f:ℕ→ℕ)(ht:Tendsto f atTop atTop):Tracked P d z (φ ∘f) p:=by obtain ⟨g,hg,hh,h⟩:= H; exact ⟨g,hg,hh.comp ht,h⟩
include hC hr hp hW
variable {n:ℕ}(M:∀ d,Cottage P d)
include M
lemma supra (D:Fin n→ℕ)(g:∀ i:Fin n,ℕ→ Label (D i))(x:∀ i:Fin n,Label (D i))(a:Points n)(h:a∈conf n)(he:∀ i,Tracked P (D i) (g i) φ (x i)): Fir.Exposes C φ (fun i p=>Fir.aperture C (fun j i=>stem P (D j) i (g j i)) (φ i) p) a (W.total n a (fun j=>W.focus none (D j) (x j))):=by
       choose k hk hz hΦ using he; let p:=fun i j=> k j (φ i);
       have hP(i:Fin n): LightP C (fun v=> stem P (D i) v (k i v)):= ((M (D i)).pointsP hC hr none (k i) (hk i)).1 -- verify
       have hpU(i:Fin n): LightP C (fun v=> stem P (D i) v (g i v)):=by
            filter_upwards [hP i,hΦ i] with j hb hi
            obtain ⟨U,hU,w⟩:=hb; obtain ⟨Y,h,hY⟩:=hi; refine ⟨U+1,by linarith only[hU],?_⟩; filter_upwards [w,hY,h.eventually_le_const zero_lt_one] with k hx h hp; have hx':= GreenP.mono (GreenP.add hx h.2) (show U+Y k≤ U+1 from add_le_add_right hp U); convert hx' using 1; abel -- k shadow k i
       let Pz(i:Fin n)(v:ℕ):=stem P (D i) v (k i v); let Vz(i:Fin n)(v:ℕ):=stem P (D i) v (g i v); have hx:= Fir.Sash.bouquet hC hr hp Vz Pz (fun i=>⟨hpU i,hP i,hΦ i⟩) a h; let X':=(W.total n a (fun j=>W.focus none (D j) (x j)))
       have hU: Exposes C φ (fun i r=> Fir.aperture C Pz (φ i) r) a X' :=by
            exact hW.exposed D (fun _=> none) x p (tendsto_pi_nhds.mpr hz) _ h -- rfl?
       have h:=hx.add hU; rw [zero_add] at h; exact h.congr (fun p=> sub_add_cancel ..)
-- Pair utility.Separate sparse.H.
omit hp hC hr hW M
open QCD.Lat
set_option quotPrecheck false
local notation "R" i:arg=> (C.A i).regulator
include hp hC hr hW M
open _root_.YM.Fir.NoteF
lemma pairLy {k:ℕ}(f:ℕ→Label d)(g:ℕ→Label k)(w:Label d)(p:Label k)(hf:Tracked P d f φ w)(hg:Tracked P k g φ p)(x:Points 2)(hx:x∈conf 2)(r:ℕ→Fin 2→ Cover)(hS:Tendsto (fun i=> pollF C 2 (φ i) (r i)) atTop (𝓝 x)): Tendsto (fun i=> ((C.A (φ i)).regulator).average ((stem P d (φ i) (f (φ i)) (r i 0))*(stem P k (φ i) (g (φ i)) (r i 1)))) atTop (𝓝 (W.total 2 x ![W.focus none d w,W.focus none k p])):=by
          let D:Fin 2→ℕ:= ![d,k]; let V(i:Fin 2):ℕ→Label (D i):=Fin.cons (α:=fun i=>ℕ→Label (D i)) f (Fin.cons (α:=fun i:Fin 1=>ℕ→Label (D i.succ)) g (fun i=>i.elim0)) i; let X(i:Fin 2):Label (D i):=Fin.cons (α:=fun i=>Label (D i)) w (Fin.cons (α:=fun i:Fin 1=>Label (D i.succ)) p (fun i=>i.elim0)) i
          have hV:=supra W hp hW hC hr M D V X x hx (fun i=>by fin_cases i; exact hf; exact hg); have hE: Tendsto (fun i:ℕ=> (i,r i)) atTop (Watch C φ x):=YM.Fir.NoteF.ride (v:=fun i=>pollF C 2 (φ i)) _ _ tendsto_id hS; have hh:= hV.comp hE
          rw [show ![_,W.focus none k p]= _ from (show ![W.focus none d w,W.focus none k p]=(fun i=>W.focus none _ (X i)) from funext fun i=>by fin_cases i <;> rfl)]
          refine hh.congr (fun i=>?_); change readS C (φ i) _ (r i)= _; unfold readS; simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]; rfl
-- representative tracked parity. hF permit gives true Mark parity.Prop use Crest. test hW via H.Domestic. For Ξ measure relative to p_N facing q. Need prove parity actor of regulator.Temt.
open Harmony
variable (T:Pollens P W)(ht:Foil P W T)(hP:P.System)(w:Label d)
include ht hP
lemma tracksP (q:Bool)(hf:Tracked P d f φ w) (hq:∀ᶠ i in atTop, moored ((P.mix d none i) (f i)).val q): T.parity (W.focus none d w)=(if q then (-1:ℂ) else 1) • W.focus none d w:=by
      -- exact identity via comparing opposite leg.Prove via nonzero.Alternative A.P.Fo Crest
      have hs : ∀ᶠ i in atTop, ∀ b:Cover,∀ V,Grass.Hom q ((stem P d i (f i)) b V):=by
             filter_upwards [hq] with i hi b U;
             -- prove grading.
             let k:=P.sym; let x:= P.mix d none i (f i); let Q:= P.candidate d (C.S.side (C.R i) (C.N i)) b; have hV : k.parity d x=(if q then (-1:ℂ) else 1) • x:= (moored_iff P.sym _ _).1 hi
             have h: Grass.grade (Q x U)=Q (k.parity d x) U:=congr_fun (hP.sections.parity ..) _; rw [hV,map_smul] at h; change Grass.Hom q (Q x U); cases q
             · rw[if_neg (by decide),one_smul] at h; exact h
             rw [if_pos rfl,neg_one_smul] at h; exact h
      let k:ℂ:= if q then -1 else 1; let x:= W.focus none d w; let P0:=T.parity; apply sub_eq_zero.mp; by_contra hv; obtain ⟨a,ha,b,hZ⟩:= hW.h.listens _ hv
      obtain ⟨r,fv,hV⟩:= hW.h.tidal (P0.symm b) none
      let V:=P.sym.parity r fv; have hh: W.focus none r V = b:=by rw [show W.focus none r V=P0 (W.focus none r fv) from (T.p ..).symm,hV]; exact P0.apply_symm_apply _
      let z:=points (![0,a]); let S:= W.total 2 z; let p:= W.focus none r fv; have hT :z∈ conf 2:=by
            intro i j h; fin_cases i <;> fin_cases j; · rfl
            · exfalso; change (0:E4) = a at h; have h0:=ha timeAxis; rw[←h] at h0; exact lt_irrefl _ h0
            · exfalso; change a= 0 at h; have h0:=ha timeAxis; rw[h] at h0; exact lt_irrefl _ h0
            rfl
      obtain ⟨g,hg⟩:= Fir.visions hC hp z
      have h(q:Label r) :Tracked P r (fun _=> q) φ q:= tracksZ (fun _=>q) q tendsto_const_nhds ⟨_,norm_nonneg _, Eventually.of_forall (fun _=> le_rfl)⟩ -- order
      let F(q:Label r) (i:ℕ):= ((C.A (φ i)).regulator).average ((stem P r (φ i) q (g i 0)) * (stem P d (φ i) (f (φ i)) (g i 1)))
      have hA:Tendsto (F fv) atTop (𝓝 (S (![p,x]))):= pairLy W hp hW hC hr M (fun _=> fv) f fv w (h fv) hf z hT g hg
      have hB:Tendsto (F V) atTop (𝓝 (S (![b,x]))):= hh ▸ pairLy W hp hW hC hr M (fun _=> V) f V w (h V) hf z hT g hg
      have hΨ:S ![p,x]= k*S ![b,x]:=by
             apply tendsto_nhds_unique hA; refine (hB.const_mul k).congr' ?_; filter_upwards [hp.eventually (hP.mixing r),hp.eventually hs] with i hi hs'
             let Y:=(C.A (φ i)).regulator; obtain ⟨F'⟩:= Dispersed.MoveR.parityP Y
             let B_:= P.mix r none (φ i); let X:=P.sym.parity r
             let z(q:Label r):=P.candidate r (C.S.side (C.R (φ i)) (C.N (φ i))) (g i 0) (B_ q)
             let Y':= stem P d (φ i) (f (φ i)) (g i 1); have hw(k):= hs' (g i 1) k; change k*Y.average (z V* Y')=Y.average _; change _=Y.average (z fv* Y'); rw [←smul_eq_mul,← map_smul]; apply F'.uses; ext1 U
             change (k • (z V * Y')) U= Grass.grade ((z fv*Y') U); simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,map_mul]
             have hX:Grass.grade (z fv U)=z V U:=by
                   have hx:= (show Grass.grade ((z fv) U)= P.candidate r (C.S.side (C.R (φ i)) (C.N (φ i))) (g i 0) (X (B_ fv)) U from congr_fun (hP.sections.parity ..) U); rw [show X (B_ fv)=B_ V from LinearEquiv.congr_fun (hi.parity none) fv] at hx; exact hx
             have hY : Grass.grade (Y' U)= k • (Y' U):=by cases q; rw [show k=(1:ℂ) from rfl,one_smul]; exact hw _; rw [show k=(-1:ℂ) from rfl,neg_one_smul]; exact hw _
             rw [hX,hY,mul_smul_comm]
      have hBr:![b,P0 x]=(⇑P0) ∘ (![p,x]:Fin 2 → W.W):= funext fun i=>by fin_cases i; exact hh.symm.trans (T.p ..).symm; rfl
      have hV':S ![b,P0 x]= S ![p,x]:=by rw[hBr]; exact ht.parity 2 z hT _
      let L: W.W→ₗ[ℂ]ℂ:= S.toLinearMap (![b,0]) 1; have hL (x:W.W): S (![b,x])=L x:=by apply congr_arg S; funext i; fin_cases i<;>simp
      apply hZ; change S _=0; rw [hL]; change L (P0 x-k • x)=0; rw[map_sub,map_smul,smul_eq_mul,←hL,←hL,hV',hΨ,sub_self]
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.tracksP
