from blowup_lab.primary_residual_layers import primary_linear_residual_layers


def test_psi_one_erases_excluded_slot_but_not_constructed_good_obligation():
    report = primary_linear_residual_layers()
    layers = {layer["layer_id"]: layer for layer in report["layers"]}
    assert layers["primary.excluded_slot"]["status_under_psi_one"] == "ERASED_UNDER_SOLVE_IDENTITY"
    assert layers["primary.constructed_good"]["status_under_psi_one"] == "PERSISTS_AS_EXPLICIT_OBLIGATION"


def test_constructed_good_is_split_into_curl_principal_and_remainder():
    report = primary_linear_residual_layers()
    ids = {layer["layer_id"] for layer in report["layers"]}
    assert "good.curl_principal" in ids
    assert "good.corrected_remainder" in ids


def test_report_does_not_claim_constructed_good_is_nonzero_or_uncancellable():
    report = primary_linear_residual_layers()
    boundary = report["claim_boundary"].lower()
    assert "does not claim constructedgood is pointwise nonzero" in boundary
    assert "cannot be cancelled" in boundary
