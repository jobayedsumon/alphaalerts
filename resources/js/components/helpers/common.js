import Swal from "sweetalert2";

export const swalSuccess = (text) => {
    Swal.fire({
        title: "Success",
        text: text,
        icon: 'success',
        confirmButtonText: 'Ok'
    });
}

export const swalError = (text) => {
    Swal.fire({
        title: "Error",
        text: text,
        icon: 'error',
        confirmButtonText: 'Ok'
    });
}

export const swalConfirm = () => {
    return Swal.fire({
        title: "Are you sure?",
        text: 'You will not be able to recover this data!',
        icon: 'warning',
        showCancelButton: true,
        confirmButtonText: 'Yes',
        cancelButtonText: 'No'
    });
}
