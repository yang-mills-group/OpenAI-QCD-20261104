import YM.Mural.Cart
/-!
# Row-wise score. The launch charges are uniform over both flavors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side} {j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
-- capture Σ.Weight.P uniform over all. Support.Pre.F.width at this clock D'.O
open MassiveQCD.Twist
variable {I E:Type}(D:DeckV c N)(D':DeckV f N)(L: YM.Next.Free.Flight j k)(d:f.val=c.val*L.L.val)(K:KernelChoices)(r β:ℝ)(hk:L.patch.Branches K su)
set_option quotPrecheck false
local notation "Fb"=> Rank→ Insertion f N
local notation "Cb"=> Rank→ Insertion c N
variable (X: Insertion f N)(Y:Insertion c N) (x y:Site c) (p q:Site f)
variable (C α:ℂ)
local notation "sP"=> performance X p q
local notation "sR"=> performance Y x y
local notation "Λ"=> (L.visit K d)
local notation "T"=> Transfer.blockMap L K d β r hk
local notation "TX"=> texel L d 0 x p
local notation "TY"=> texel L d 0 y q
variable (V V₀: TokenP) (B:ℕ)(a b v w w₀:ℝ)(e v₁ v₂:ℂ)(Z : Fb) (Zi: I→Fb)
local notation "Zr" => (aisle V D x y (α*C)) -- signature maybe aisle p.
local notation "wx"=> TokenP.t V
lemma strip_h (x:Site c)(S W:Support c) (p:PrintR c N Rank I E)(h:S⊆W)(hi:p.Fides (fun _=>x) W D.O (fieldD x y)): p.Fides (fun _=>x) S D.O (fieldD x y):=by
    constructor <;> intro g
    · obtain ⟨ht,hV,hw⟩:=hi.tinted g; exact ⟨fun i=>{(ht i) with boast:= fun j=> h.trans ((ht i).boast _)},hV,hw⟩
    obtain ⟨ht,hV,hw⟩:=hi.rise g; exact ⟨fun i=>{(ht i) with rails:= fun j=> h.trans ((ht i).rails _)}, hV,hw⟩
variable {B}
lemma song_h {F: Cb} (h:D.O.B ≤ B) (hp:Boast D F x y (Lattice.halo B {x}) V.t V.f V.e V.k V.v V.w V.s (α*C)): F∈ aisle V D x y (α*C):=by
     obtain ⟨I,J,hI,hJ,V',hr,ha,hf⟩:= hp.expo; refine ⟨_,_,hI,hJ,V', strip_h D y _ _ _ _ (Corona.halo_mono h (Subset.refl _)) hr,ha,hf⟩
variable (H:D.O.B≤B)(ht: V.t=V₀.t) (hArk:Ark D D' L d K r β C x y p q V₀.f B V.t V.f a b v w V.s V.w V.v V.e V.k w₀) (he:Y= (Transfer.blockMap L K d β r hk) X)
variable (hf:∀ i,Summable fun j=> ‖D'.K.warp j i‖)(hV:∀ i,Summable fun j=> ‖D.K.warp j i‖)(hX:∀ i,X i= α • D'.density i)
variable (W₀:ℝ)
variable (Hθ:1≤ V.t)(hθ:1 ≤V₀.f)(hFunds:0 ≤ b)(hl:1 ≤ v)(hr:0≤w)(hk':0≤a)(h1:0≤w₀)(hα:1≤V.f)(hk1:1≤ V.w)(hVf:0≤V.k)(hv:0≤V.e)
variable (hx:separation ((L.visit K d).ratio.embed x) p≤ arctic L.L j)(hy:separation ((L.visit K d).ratio.embed y) q≤ arctic L.L j)(hz: separation p q≤ berthD j)
include hX Hθ hθ hFunds hl hr hk' H hArk hf
lemma con (H:‖e‖≤w₀): (fun i=>rebirth L d K r β hk X x y p q e i)∈ aisle V D x y (α*C):=by
    apply song_h _ x y C α V ‹D.O.B≤B›
    exact stocks D D' L d K r β hk C e X hX x y p q V₀.f B V.t V.f a b v w V.s V.w V.v V.e V.k hArk hf Hθ hθ hFunds hl hr hk' H -- sig
omit hX hFunds hr
include h1 hx hy hz ht
variable (hSize:2*L.patch.radius<f.val)(he':a≤V₀.e)(hw:a≤ V₀.k)(hh:v≤V₀.w)(hB: 2* arctic L.L j+berthD j≤D'.O.B)
local notation "W"=> billow L d K r β hk x y p q
variable (z:ℂ) (eB u₁:ℝ)(hW:∀ X:Mat,∀ i j:Hue,‖X i j‖≤ W₀*‖X‖)(hG:0≤W₀)(hΞ:‖z‖*(W₀*Kit.scale L.L)^2≤ eB)(hLoan:(Fintype.card Rank:ℝ)*(eB*V₀.v) ≤ b)(hν:(Fintype.card Rank:ℝ)*(eB*V₀.s) ≤ w)
include hSize he' hw hh hB hW hG hΞ hLoan hν
lemma mettle (F:Rank→Insertion f N)(hp:F∈ aisle V₀ D' p q α): z • ((W) F)∈ aisle V D x y (α*C):=by
      apply song_h _ x y C α V H
      have hZ':Boast D' F p q (Lattice.halo D'.O.B {p}) V.t V₀.f V₀.e V₀.k V₀.v V₀.w V₀.s α:=ht.symm ▸ (?_) -- cast tactic? simp replacing
      · exact conveys D D' L d K r β hk C x y p q V₀.f B V.t V.f a b v w V.s V.w V.v V.e V.k hArk hf Hθ hθ hl hk' h1 hSize hx hy hz F hZ' he' hw hh hB z W₀ eB hW hG hΞ hLoan hν -- check
      exact ‹F ∈ _›
omit hx hy hz ht hSize he' hw hh hB hW hG hΞ hLoan hν h1 Hθ hθ hl hk' hf hArk H
variable (g₁ g₂:ℝ)
lemma noted (F: Fb)(hP:ClaimP (aisle V₀ D' p q α) sP F g₁ g₂) (he:Y= T X)(h1V:∀ F'∈ aisle V₀ D' p q α,z • ((W) F')∈ (Zr))(hVh:(fun i=> rebirth L d K r β hk X x y p q e i) ∈ aisle V D x y (α*C)) (hk: e ≠0) (hz:z≠0)(hu:2*L.patch.radius<f.val) : ClaimP Zr sR ((W) F) (g₁*Kit.scale L.L^2) (g₁*‖e⁻¹‖+g₂*‖z⁻¹‖) :=by
    obtain ⟨c,F',hp,hΓ,hQ⟩:= hP.costP
    let b₁:= lightS L d 0 x p*star (lightS L d 0 y q); let p₁:= fun i=> rebirth L d K r β ‹L.patch.Branches K su› X x y p q e i; let f':= e⁻¹ • p₁
    have hx : Worth Zr f' ‖e⁻¹‖:=by simpa only [mul_one] using Worth.rotate (e⁻¹) (Worth.oneP p₁ hVh)
    have hv : Worth Zr ((W) F') (g₂* ‖z⁻¹‖):=by
       apply Worth.move (W) hΓ _ (norm_nonneg _); intro x' h; have he:=Worth.rotate z⁻¹ (Worth.oneP _ (h1V x' h)); rwa [inv_smul_smul₀ hz,mul_one] at he
    refine ⟨c*b₁,c • f'+(W) F',?_ ,Worth.added (Worth.fuel (Worth.rotate c hx) ?_) hv,?_⟩
    · rw [norm_mul, pow_two]; apply mul_le_mul hp _ (norm_nonneg _) ((norm_nonneg _).trans hp); unfold b₁; rw[norm_mul,norm_star]; exact mul_le_mul (light_bound p L d x hu _) (light_bound q L d y hu _) (norm_nonneg _) (Kit.scale_pos _).le
    · exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    rw [hQ,map_add,map_smul,tune L d K r β _ X Y x y p q he e hk, smul_add,mul_smul c b₁]; rw [add_assoc]
end YM.QCD.Comet
#print axioms YM.QCD.Comet.noted
#print axioms YM.QCD.Comet.mettle
