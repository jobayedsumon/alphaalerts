import fetchWrapper from "./fetchWrapper";

export const connectDiscord = () => {
    const token = localStorage.getItem('token');
    window.location.href = '/api/discord-connect?token=' + token;
}

export const disconnectDiscord = () => {
    fetchWrapper.get('/api/discord-disconnect')
        .then(response => {
            const data = response.data;
            if (data.status === 'success') {
                window.location.reload();
            }
        }).catch(error => {
    });
}
