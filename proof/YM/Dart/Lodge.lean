import YM.Dart.Book
/-!
# Initial quantity universal estimates and orientation. Fuel for barrier.
Index-specific costs.S.Choice P per actual Beta at funding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PlaneG
open Gallery PrismD Civic
open Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate 
open Cove Creek Stamp
variable {H:YM.Source.Hol su}(U:Lining.Temper.Collage.Exhibit H)(θ:SourceRead.TaperHol)
variable {X:Drape} (s:ℕ)
namespace Asset
variable {s}(V:Asset X s) (l:List Axis)
include V
lemma equity (d:ℕ) : ∃ p :Label d, TravelsP θ (evoc X l) (passport d p):=by
    let W:= evoc X l; obtain ⟨A⟩:= Source.Hol.exists_ode su -- term.Nonempty
    obtain ⟨p,M,hM⟩:= peony θ A W 0 s d (V.bore l) -- no braces.fix
    let n:Side:=⟨M+1,Nat.succ_pos _⟩; have hv(u:su.El): tint u d p=p:=by
       obtain ⟨N,hN⟩:= travelsZ θ p u ⟨M,hM⟩; let n:Side:=⟨M+N+1,Nat.succ_pos _⟩; have hz: whereby u W=W:=funext fun n=> funext fun o=> profileEv V.shape l n o (gways u n); rw [hz] at hN; let o:Cover:=0; exact Subtype.ext (Beacon.chooses θ o (Submodule.coe_mem (tinted d u p)) p.property (hN n o (by change N ≤ M+N+1; omega)) (hM n o (by change M ≤ M+N+1; omega)))
    let q: Label d:=⟨_,(label_law p.val).mpr ⟨p.property, fun u=> congr_arg Subtype.val (hv u)⟩⟩; exact ⟨q,M,hM⟩
lemma heritage (n:Side)(o:Cover) : Gallery.moon (polarity s) (evoc X l n o):=by
     intro A; have hx:= grade_phase _ _ (convoy (V.bore l) A o); by_cases h:Odd s
     · rw [show polarity s=true from decide_eq_true h]; rw[h.neg_one_pow,neg_one_smul] at hx; exact hx
     rw [show polarity s=false from decide_eq_false h]; rw[(Nat.not_odd_iff_even.mp h).neg_one_pow,one_smul] at hx; exact hx
omit V
noncomputable def game (s:ℕ)(v:ℝ):ℝ := (v^s)⁻¹
noncomputable def tileD (X:Drape)(s:ℕ)(v:ℝ)(l:List Axis):Drape:=evoc ((game s v:ℂ) • X) l
include V
lemma lanternD : ∃ C:ℝ,0 ≤ C ∧ ∀ᶠ r:ℕ in atTop,∀ k m f j:ℕ,∃ D:ℝ,1≤D∧∀(P:BudgetPoint)(K:Side)(b:Cover) (v:ℝ), 0<v→ P.order=k→P.power=m→2*(r+1)< K.val→ Flame ⇑((tileD X s v l) K b) P (pot (r+1) K b) (wrap K b) v f j D ∧∀ U:Grid K, Creek.load (fun _=>v) ((tileD X s v l) K b U) ≤ C:=by
     obtain ⟨C,hC,h⟩:= lantern (evoc X l) 0 _ (V.bore l); refine ⟨C,hC,?_⟩; filter_upwards [lease_flame (evoc X l) 0 _ (V.bore l)] with r hr k m f j; obtain ⟨A,hA,hφ⟩:= hr k m f j; refine ⟨max 1 A, le_max_left ..,fun P K b v hv he hm hB=>?_⟩; let T:= v^s; let t:= game s v; have ht:0<t:=inv_pos.mpr (pow_pos hv _); have hs:t*T=1:= inv_mul_cancel₀ (pow_pos hv _).ne'; unfold tileD; rw[layered]; constructor
     · have he:= Girdle.flare_by P _ _ (hφ P K b v hv hm he hB) (t:ℂ); apply leFlame he; rw[Complex.norm_real,Real.norm_of_nonneg ht.le]; unfold levy; rw[pow_zero,one_mul,mul_left_comm, show t*v^s=1 from hs,mul_one]; exact le_max_right ..
     intro i; change load _ ((↑t:ℂ) • _ ) ≤ _; rw[load_scale,Complex.norm_real,Real.norm_of_nonneg ht.le]; exact (mul_le_mul_of_nonneg_left (h v hv K b i) ht.le).trans_eq (by rw [←mul_assoc, show t*v^s=1 from hs, one_mul])
-- Capsule budget.
lemma coversD (Lx:Label d)(hL:TravelsP θ (evoc X l) (passport d Lx)): ∃ M:ℕ, ∃ J:ℝ,0≤J∧∀ᶠ r:ℕ in atTop,∀ k m f j r₀:ℕ,∀ α β t:ℝ,0≤t→Pilot θ U d k m f j r₀ α β→∃ D:ℝ, 1 ≤ D∧ ∀(P:BudgetPoint)(K:Side)(b:Cover)(v L σ ρ Φ ξ:ℝ), M≤ K.val→ 1 ≤ v→0 ≤L → P.order=k→P.power=m→ max r r₀+1≤ P.B→30*(r₀+1) ≤ K.val→2*(r+1)<K.val → (∀ y:Label d,∀ F:Grid K, Creek.load (fun _=>v) (graphs d U b y F)≤ L*wealth y.val P.threshold v) →0≤ ρ→ D≤Φ → (J + 2*(L*D))*Real.exp (4*81) ≤ ξ→ let Y:= (game s v:ℂ) • Lx; Stamp.Volume θ U P b r₀ (tileD X s v l K b) Y f j (polarity s) t σ v Φ ρ ξ ∧wealth Y.val P.threshold v ≤ Φ:=by
    obtain ⟨M,hM⟩:=hL; obtain ⟨J,hJ,hC⟩:= lanternD V l; refine ⟨M,J,hJ,?_⟩; filter_upwards [hC] with r h k m f j r₀ α β t ht hp; obtain ⟨D,hD,h⟩:=h k m f j
    let a:= α*D; let Dh:= max a ((D+β*a)*Real.exp (81*t)); have ha:1 ≤ a:= one_le_mul_of_one_le_of_one_le hp.light hD; refine ⟨Dh,ha.trans (le_max_left ..),fun P K b v L σ ρ Φ ξ hB hv h_ hm hk hu hS hV he hρ hΦ hξ=>?_⟩
    intro Y; let F:=tileD X s v l; let A:=F K b; have hA:=h P K b v (zero_lt_one.trans_le hv) hm hk hV
    have hy: Beacon.ActionTest θ b A Y.val:=by unfold A F tileD; rw[layered]; exact PrismD.constA b θ _ _ _ (hM K b hB)
    have hx:wealth Y.val P.threshold v ≤ a:= hp.earn _ _ _ _ _ _ _ _ hm hk (zero_lt_one.trans_le hv) hA.1 hy -- hv maybe nonneg
    have hF:= profileEv (x:= (↑(game s v):ℂ) • X) (fun i o=> RP.invariant_smul _ (V.shape i o) _) l K b
    have h :moon (polarity s) A:=by
         unfold A F tileD; rw[layered]; exact fun i=>(heritage V l K b i).smul _
    have hq: wealth Y.val P.threshold v≤Dh:=hx.trans (le_max_left ..); refine ⟨?_,hq.trans hΦ⟩
    apply Stamp.gain θ U b Y A v D J P _ hp hm hk (max r r₀) (r+1) (le_max_right ..) (Nat.add_le_add_right (le_max_left ..) _) hu hS ht hv hy hF h hA.1 hA.2 he h_ hρ
    · apply le_trans (b:=Dh) _ hΦ; apply le_trans _ (le_max_right ..); gcongr; · exact zero_le_one.trans hp.funds
    apply le_trans _ hξ; gcongr
end Asset
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.equity
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.coversD
